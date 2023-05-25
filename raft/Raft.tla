(*
Author: Jack Vanlightly.
Model checking optimized fork of the original Raft spec by Diego Ongaro: https://github.com/ongardie/raft.tla.

Summary of changes:
    - Updated message helpers.
        - Prevent resending the same message multiple times (unless explicity via the duplicate action).
        - Can only receive a message that hasn't been delivered yet.
    - Optimized for model checking (reduction in state space).
        - Removed history variables (using simple invariants instead).
        - Decomposed "receive" into separate actions.
        - Compressed multi-step AppendEntriesRequest processing into one.
        - Compressed timeout and RequestVote into single action.
        - Server directly votes for itself in an election (it doesn't send itself a vote request).
    - Fixed some bugs.
        - Adding the same value over and over again.
        - Allowing actions to remain enabled producing odd results.

Notes on action enablement.
    - Send is only enabled if the message has not been previously sent.
    - This is leveraged to disable actions once executed, such as sending a specific AppendEntriesRequest.
    - It won't be sent again, so no need for extra variables to track that.

12/06/2023
Federico Valeri
- Added constants validation.
- Variable currentTerm initialized to 0 on first boot.
- Added note on livenees property (can't be used with symmetry sets).
- Moved helper operators to Utils module.
*)
---- MODULE Raft ----

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs.
CONSTANTS Servers

\* The set of values that can go into the log.
CONSTANTS Values

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types.
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

\* Used for filtering messages under different circumstance.
CONSTANTS EqualTerm, LessOrEqualTerm

\* Reduce the state space by limiting the number of elections and restarts.
CONSTANTS MaxElections, MaxRestarts

\* Constants validation.
ASSUME
  /\ Servers # {}
  /\ Values # {}
  /\ MaxElections \in Nat
  /\ MaxRestarts \in Nat

----

\* A bag of records representing requests and responses sent from one server to another.
\* TLAPS doesn't support the Bags module, so this is a function mapping Message to Nat.
VARIABLES messages

\* Per server variables (functions with domain Server).

\* The server's term number.
VARIABLES currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLES state
\* The candidate the server voted for in its current term, or Nil if it hasn't voted for any.
VARIABLES votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries.
\* The index into this sequence is the index of the log entry.
\* Unfortunately, the Sequence module defines Head(s) as the entry with index 1, so be careful not to use that!
VARIABLES log
\* The index of the latest entry in the log the state machine may apply.
VARIABLES commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates.

\* The set of servers from which the candidate has received a vote in its currentTerm.
VARIABLES votesGranted
candidateVars == <<votesGranted>>

\* The following variables are used only on leaders.

\* The next entry to send to each follower.
VARIABLES nextIndex
\* The latest entry that each follower has acknowledged is the same as the leader's.
\* This is used to calculate commitIndex on the leader.
VARIABLES matchIndex
\* Used to track which peers a leader is waiting on a response for.
\* Used for one-at-a-time AppendEntries RPCs.
\* Not really required but permitting out of order requests explodes the state space.
VARIABLES pendingResponse
leaderVars == <<nextIndex, matchIndex, pendingResponse>>

\* Auxiliary variables (used for state space control, invariants etc).

\* The values that have been received from a client and whether the value has been acked back to the client.
\* Used in invariants to detect data loss.
VARIABLES acked
\* Counter for elections and restarts. Used used to control state space.
VARIABLES electionCtr, restartCtr
auxVars == <<acked, electionCtr, restartCtr>>

----

\* All variables. Used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, auxVars>>
\* This view is used by TLC to distinguish states, instead of using all variables.
varsWithoutAux == <<messages, serverVars, candidateVars, leaderVars, logVars>>
\* Used to restrict the state space by skipping symmetrics states.
\* The set must not be used in CHOOSE or liveness expressions.
symmServers == Permutations(Servers)

\* The set of all quorums.
\* This calculates simple majorities, but the only important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Servers) : Cardinality(i) * 2 > Cardinality(Servers)}

\* Import utils.
Utils == INSTANCE Utils

----

InitServerVars ==
    /\ currentTerm = [i \in Servers |-> 0]
    /\ state       = [i \in Servers |-> Follower]
    /\ votedFor    = [i \in Servers |-> Nil]
InitCandidateVars == votesGranted = [i \in Servers |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the leader does not send itself messages.
\* It's still easier to include these in the functions.
InitLeaderVars ==
    /\ nextIndex  = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
InitLogVars ==
    /\ log             = [i \in Servers |-> <<>>]
    /\ commitIndex     = [i \in Servers |-> 0]
    /\ pendingResponse = [i \in Servers |-> [j \in Servers |-> FALSE]]
InitAuxVars ==
    /\ electionCtr = 0
    /\ restartCtr = 0
    /\ acked = [v \in Values |-> Nil]

Init ==
    /\ messages = [m \in {} |-> 0]
    /\ InitServerVars
    /\ InitCandidateVars
    /\ InitLeaderVars
    /\ InitLogVars
    /\ InitAuxVars

----

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor and log.
Restart(i) ==
    /\ restartCtr < MaxRestarts
    /\ state'           = [state EXCEPT ![i] = Follower]
    /\ votesGranted'    = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'       = [nextIndex EXCEPT ![i] = [j \in Servers |-> 1]]
    /\ matchIndex'      = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] = [j \in Servers |-> FALSE]]
    /\ commitIndex'     = [commitIndex EXCEPT ![i] = 0]
    /\ restartCtr'      = restartCtr + 1
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, acked, electionCtr>>

\* Combined Timeout and RequestVote of the original spec to reduce state space.
\* Server i times out and starts a new election.
\* Sends a RequestVote request to all peers but not itself.
RequestVote(i) ==
    /\ electionCtr < MaxElections
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ electionCtr' = electionCtr + 1
    /\ Utils!SendMultipleOnce(
           {[mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i] + 1,
             mlastLogTerm  |-> Utils!LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j] : j \in Servers \ {i}})
    /\ UNCHANGED <<acked, leaderVars, logVars, restartCtr>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i # j
    /\ state[i] = Leader
    /\ pendingResponse[i][j] = FALSE \* not already waiting for a response
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* send up to 1 entry, constrained by the end of the log
           lastEntry == Utils!Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN
          /\ pendingResponse' = [pendingResponse EXCEPT ![i][j] = TRUE]
          /\ Utils!Send([mtype    |-> AppendEntriesRequest,
                   mterm          |-> currentTerm[i],
                   mprevLogIndex  |-> prevLogIndex,
                   mprevLogTerm   |-> prevLogTerm,
                   mentries       |-> entries,
                   mcommitIndex   |-> Utils!Min({commitIndex[i], lastEntry}),
                   msource        |-> i,
                   mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, nextIndex, matchIndex, logVars, auxVars>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] = [j \in Servers |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] = [j \in Servers |-> FALSE]]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, auxVars>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ acked[v] = Nil \* prevent submitting the same value repeatedly
    /\ LET entry == [term |-> currentTerm[i], value |-> v]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           /\ acked' = [acked EXCEPT ![v] = FALSE]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, electionCtr, restartCtr>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses, in part to minimize atomic regions,
\* and in part so that leaders of single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* the set of servers that agree up through index
           Agree(index) == {i} \cup {k \in Servers : matchIndex[i][k] >= index}
           \* the maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) : Agree(index) \in Quorum}
           \* new value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes # {}
                 /\ log[i][Utils!Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Utils!Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN
          /\ commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ acked' = [v \in Values |->
                        IF acked[v] = FALSE
                        THEN v \in {log[i][index].value : index \in commitIndex[i]+1..newCommitIndex}
                        ELSE acked[v]]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log,
                   pendingResponse, electionCtr, restartCtr>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm ==
    \E m \in DOMAIN messages :
        /\ m.mterm > currentTerm[m.mdest]
        /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
        /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
        /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
           \* messages is unchanged so m can be processed further
        /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>

\* Server i receives a RequestVote request from server j with m.mterm <= currentTerm[i].
HandleRequestVoteRequest ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == \/ m.mlastLogTerm > Utils!LastTerm(log[i])
                        \/ /\ m.mlastLogTerm = Utils!LastTerm(log[i])
                           /\ m.mlastLogIndex >= Len(log[i])
               grant == /\ m.mterm = currentTerm[i]
                        /\ logOk
                        /\ votedFor[i] \in {Nil, j}
            IN /\ m.mterm <= currentTerm[i]
               /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
                  \/ ~grant /\ UNCHANGED votedFor
               /\ Utils!Reply([mtype  |-> RequestVoteResponse,
                         mterm        |-> currentTerm[i],
                         mvoteGranted |-> grant,
                         msource      |-> i,
                         mdest        |-> j],
                         m)
               /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, auxVars>>

\* Server i receives a RequestVote response from server j with m.mterm = currentTerm[i].
HandleRequestVoteResponse ==
    \E m \in DOMAIN messages :
        \* this counts votes even when the current state is not Candidate,
        \* but they won't be looked at, so it doesn't matter
        /\ Utils!ReceivableMessage(m, RequestVoteResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ \/ /\ m.mvoteGranted
                    /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                              votesGranted[i] \cup {j}]
                 \/ /\ ~m.mvoteGranted
                    /\ UNCHANGED <<votesGranted>>
              /\ Utils!Discard(m)
              /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, auxVars>>

\* Server i receives an invalid AppendEntries request from server j.
\* Either the term of the message is stale or the message entry is too high (beyond the last log entry + 1).
RejectAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, AppendEntriesRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == Utils!LogOk(i, m)
           IN  /\ \/ m.mterm < currentTerm[i]
                  \/ /\ m.mterm = currentTerm[i]
                     /\ state[i] = Follower
                     /\ ~logOk
               /\ Utils!Reply([mtype |-> AppendEntriesResponse,
                         mterm       |-> currentTerm[i],
                         msuccess    |-> FALSE,
                         mmatchIndex |-> 0,
                         msource     |-> i,
                         mdest       |-> j],
                         m)
               /\ UNCHANGED <<state, candidateVars, leaderVars, serverVars, logVars, auxVars>>

\* Server i receives a valid AppendEntries request from server j.
\* The original spec had to three sub actions, this version is compressed.
\* In one step it can: truncate the log, append an entry to the log, respond to the leader.
AcceptAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, AppendEntriesRequest, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == Utils!LogOk(i, m)
               index == m.mprevLogIndex + 1
           IN
              /\ state[i] \in {Follower, Candidate}
              /\ logOk
              /\ LET newLog == CASE Utils!CanAppend(m, i) ->
                                        [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
                                  [] Utils!NeedsTruncation(m, i, index) /\ m.mentries # <<>> ->
                                        [log EXCEPT ![i] = Append(Utils!TruncateLog(m, i), m.mentries[1])]
                                  [] Utils!NeedsTruncation(m, i, index) /\ m.mentries = <<>> ->
                                        [log EXCEPT ![i] = Utils!TruncateLog(m, i)]
                                  [] OTHER -> log
                 IN
                    /\ state' = [state EXCEPT ![i] = Follower]
                    /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                    /\ log' = newLog
                    /\ Utils!Reply([mtype |-> AppendEntriesResponse,
                              mterm       |-> currentTerm[i],
                              msuccess    |-> TRUE,
                              mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                              msource     |-> i,
                              mdest       |-> j],
                              m)
                    /\ UNCHANGED <<candidateVars, leaderVars, votedFor, currentTerm, auxVars>>

\* Server i receives an AppendEntries response from server j with m.mterm = currentTerm[i].
HandleAppendEntriesResponse ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, AppendEntriesResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ \/ /\ m.msuccess \* successful
                    /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                 \/ /\ ~m.msuccess \* not successful
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Utils!Max({nextIndex[i][j] - 1, 1})]
                    /\ UNCHANGED <<matchIndex>>
              /\ pendingResponse' = [pendingResponse EXCEPT ![i][j] = FALSE]
              /\ Utils!Discard(m)
              /\ UNCHANGED <<serverVars, candidateVars, logVars, auxVars>>

----

Next ==
    \/ \E i \in Servers : Restart(i)
    \/ \E i \in Servers : RequestVote(i)
    \/ \E i \in Servers : BecomeLeader(i)
    \/ \E i \in Servers, v \in Values : ClientRequest(i, v)
    \/ \E i \in Servers : AdvanceCommitIndex(i)
    \/ \E i,j \in Servers : AppendEntries(i, j)
    \/ UpdateTerm
    \/ HandleRequestVoteRequest
    \/ HandleRequestVoteResponse
    \/ RejectAppendEntriesRequest
    \/ AcceptAppendEntriesRequest
    \/ HandleAppendEntriesResponse
    \*\/ \E m \in DOMAIN messages : Utils!DuplicateMessage(m)
    \*\/ \E m \in DOMAIN messages : Utils!DropMessage(m)

Spec == Init /\ [][Next]_vars

----

\* INVARIANT: the log index is consistent across all servers
\* (on those servers whose commitIndex is equal or higher than the index).
NoLogDivergence ==
    \A s1, s2 \in Servers :
        IF s1 = s2
        THEN TRUE
        ELSE
            LET lowestCommonCi == Utils!MinCommitIndex(s1, s2)
            IN IF lowestCommonCi > 0
               THEN \A index \in 1..lowestCommonCi : log[s1][index] = log[s2][index]
               ELSE TRUE

\* INVARIANT: A non-stale leader cannot be missing an acknowledged value.
LeaderHasAllAckedValues ==
    \* for every acknowledged value
    \A v \in Values :
        IF acked[v] = TRUE
        THEN
            \* there does not exist a server that
            ~\E i \in Servers :
                \* is a leader
                /\ state[i] = Leader
                \* and which is the newest leader (aka not stale)
                /\ ~\E l \in Servers :
                    /\ l # i
                    /\ currentTerm[l] > currentTerm[i]
                \* and that is missing the value
                /\ ~\E index \in DOMAIN log[i] :
                    log[i][index].value = v
        ELSE TRUE

\* INVARIANT: There cannot be a committed entry that is not at majority quorum.
\* Don't use this invariant when allowing data loss on a server.
CommittedEntriesReachMajority ==
    IF \E i \in Servers : state[i] = Leader /\ commitIndex[i] > 0
    THEN \E i \in Servers :
           /\ state[i] = Leader
           /\ commitIndex[i] > 0
           /\ \E quorum \in SUBSET Servers :
               /\ Cardinality(quorum) = (Cardinality(Servers) \div 2) + 1
               /\ i \in quorum
               /\ \A j \in quorum :
                   /\ Len(log[j]) >= commitIndex[i]
                   /\ log[j][commitIndex[i]] = log[i][commitIndex[i]]
    ELSE TRUE

\* LIVENESS: A client value will either get committed and be fully replicated or it will be truncated
\* and not be found on any server log. Note that due to the number of elections being limited, the last
\* possible election could fail and prevent progress, so this liveness formula only applies in cases a
\* behaviour does not end with all elections used up and no elected leader. Additionally, you cannot use
\* symmetry sets if the set is used in a liveness property.
ValuesNotStuck == \A v \in Values : []<>Utils!ValueAllOrNothing(v)

====
