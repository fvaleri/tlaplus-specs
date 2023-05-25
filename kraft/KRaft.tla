(*
Author: Jack Vanlightly
This specification is based on (with heavy modification) the original Raft specification
by Diego Ongaro which can be found here: https://github.com/ongardie/raft.tla

This is a specification that has been reverse engineered from the Kafka KRaft implementation.
It makes some effort to reuse some of the functions of the implementation in order to
ensure it is accurately modelling the behaviour.

KRaft is a pull variant of Raft, which is push based.

Note the following messages are not modelled:
- BeginQuorumResponse as this is only required by the implementation for liveness.
  If the leader doesn't receive a response it resends the BeginQuorumRequest. However,
  in the specification, message retries are implicit and so explicit retries are not required.
- EndQuorumRequest/Response as this exists as an optimization for a leader
  that gracefully shutsdown. It is not needed for correctness and so is not included.
- FetchSnapshotRequest/Response. This is a straight forward optimization
  and so has not been explicitly modelled.

The KRaft implementation uses a cache object as an index for epochs and their start offsets which is required
for leaders to be able to give followers the information they need to truncate their logs. This specification
does not model this cache but simply looks up this information from the log itself.

State transitions (taken from https://github.com/apache/kafka/blob/trunk/raft/src/main/java/org/apache/kafka/raft/QuorumState.java):
Unattached|Resigned transitions to:
    Unattached: After learning of a new election with a higher epoch
    Voted: After granting a vote to a candidate
    Candidate: After expiration of the election timeout
    Follower: After discovering a leader with an equal or larger epoch

Voted transitions to:
    Unattached: After learning of a new election with a higher epoch
    Candidate: After expiration of the election timeout

Candidate transitions to:
    Unattached: After learning of a new election with a higher epoch
    Candidate: After expiration of the election timeout
    Leader: After receiving a majority of votes

Leader transitions to:
    Unattached: After learning of a new election with a higher epoch
    Resigned: When shutting down gracefully

Follower transitions to:
    Unattached: After learning of a new election with a higher epoch
    Candidate: After expiration of the fetch timeout
    Follower: After discovering a leader with a larger epoch

28/06/2023
Federico Valeri
- Added constants validation.
- Variable currentEpoch initialized to 0 on first boot.
- Added note on livenees property that can't be used with symmetry sets.
- Moved helper operators to Utils module.
*)
---- MODULE KRaft ----

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs.
CONSTANTS Servers

\* The set of requests that can go into the log.
CONSTANTS Values

\* Server states.
CONSTANTS Follower, Candidate, Leader, Unattached, Voted

\* A reserved value.
CONSTANTS Nil

\* Message types.
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          BeginQuorumRequest, BeginQuorumResponse,
          EndQuorumRequest,
          FetchRequest, FetchResponse

\* Fetch response codes.
CONSTANTS Ok, NotOk, Diverging

\* Errors.
CONSTANTS FencedLeaderEpoch, NotLeader, UnknownLeader

\* Special state that indicates a server has entered an illegal state.
CONSTANTS IllegalState

\* Used for filtering messages under different circumstances.
CONSTANTS AnyEpoch, EqualEpoch

\* Limiting state space by limiting the number of elections and restarts.
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

\* The server's epoch number (the Raft term).
VARIABLES currentEpoch
\* The server's state (Follower, Candidate etc).
VARIABLES state
\* The candidate the server voted for in its current epoch.
VARIABLES votedFor
\* The peer that the server believes is the current leader.
VARIABLES leader
\* Tracks the currently pending fetch request of a follower.
VARIABLES pendingFetch
serverVars == <<currentEpoch, state, votedFor, leader, pendingFetch>>

\* A Sequence of log entries. The offset into this sequence is the offset of the log entry.
\* Unfortunately, the Sequence module defines Head(s) as the entry with offset 1, so be careful not to use that!
VARIABLES log
\* The offset of the latest entry in the log the state machine may apply.
VARIABLES highWatermark
logVars == <<log, highWatermark>>

\* The following variables are used only on candidates.

\* The set of servers from which the candidate has received a vote in its currentEpoch.
VARIABLES votesGranted
candidateVars == <<votesGranted>>

\* The following variables are used only on leaders.

\* The latest entry that each follower has acknowledged is the same as the leader's.
\* This is used to calculate highWatermark on the leader.
VARIABLES endOffset
leaderVars == <<endOffset>>

\* Auxilliary variables (used for state-space control, invariants etc).

\* The values that have been received from a client and whether the value has been acked back to the client.
\* Used in invariants to detect data loss.
VARIABLES acked
\* Counter for elections and restarts. Used used to control state space.
VARIABLES electionCtr, restartCtr
auxVars == <<acked, electionCtr, restartCtr>>

----

\* All variables. Used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, auxVars>>
varsWithoutAux == <<messages, serverVars, candidateVars, leaderVars, logVars, acked>>
symmServers == Permutations(Servers)
symmValues == Permutations(Values)

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Servers) : Cardinality(i) * 2 > Cardinality(Servers)}

\* Import utils.
Utils == INSTANCE Utils

----

InitServerVars == /\ currentEpoch = [i \in Servers |-> 0]
                  /\ state        = [i \in Servers |-> Unattached]
                  /\ leader       = [i \in Servers |-> Nil]
                  /\ votedFor     = [i \in Servers |-> Nil]
                  /\ pendingFetch = [i \in Servers |-> Nil]
InitCandidateVars == /\ votesGranted = [i \in Servers |-> {}]
InitLeaderVars == /\ endOffset = [i \in Servers |-> [j \in Servers |-> 0]]
InitLogVars == /\ log           = [i \in Servers |-> <<>>]
               /\ highWatermark = [i \in Servers |-> 0]
InitAuxVars == /\ electionCtr = 0
               /\ restartCtr = 0
               /\ acked = [v \in Values |-> Nil]

Init == /\ messages = [m \in {} |-> 0]
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitAuxVars

----

\* Server i restarts from stable storage.
\* It loses everything but its currentEpoch, votedFor and log.
Restart(i) ==
    /\ restartCtr < MaxRestarts
    /\ state'         = [state EXCEPT ![i] = Follower]
    /\ leader'        = [leader EXCEPT ![i] = Nil]
    /\ votesGranted'  = [votesGranted EXCEPT ![i] = {}]
    /\ endOffset'     = [endOffset EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ highWatermark' = [highWatermark EXCEPT ![i] = 0]
    /\ pendingFetch'  = [pendingFetch EXCEPT ![i] = Nil]
    /\ restartCtr'    = restartCtr + 1
    /\ UNCHANGED <<messages, currentEpoch, votedFor, log, acked, electionCtr>>

\* Combined Timeout and RequestVote of the original spec to reduce state space.
\* Server i times out and starts a new election.
\* Sends a RequestVote request to all peers but not itself.
RequestVote(i) ==
    /\ electionCtr < MaxElections
    /\ state[i] \in {Follower, Candidate, Unattached}
    /\ state'        = [state EXCEPT ![i] = Candidate]
    /\ currentEpoch' = [currentEpoch EXCEPT ![i] = currentEpoch[i] + 1]
    /\ leader'       = [leader EXCEPT ![i] = Nil]
    /\ votedFor'     = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
    /\ electionCtr'  = electionCtr + 1
    /\ Utils!SendMultipleOnce(
           {[mtype          |-> RequestVoteRequest,
             mepoch         |-> currentEpoch[i] + 1,
             mlastLogEpoch  |-> Utils!LastEpoch(log[i]),
             mlastLogOffset |-> Len(log[i]),
             msource        |-> i,
             mdest          |-> j] : j \in Servers \ {i}})
    /\ UNCHANGED <<acked, leaderVars, logVars, restartCtr>>

\* Server i receives a RequestVote request from server j.
\* Server i will vote for j if:
\* 1) epoch of j >= epoch of i
\* 2) last entry of i is <= to the last entry of j
\* 3) i has not already voted for a different server
HandleRequestVoteRequest ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, RequestVoteRequest, AnyEpoch)
        /\ LET i     == m.mdest
               j     == m.msource
               error    == IF m.mepoch < currentEpoch[i]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               state0   == IF m.mepoch > currentEpoch[i]
                           THEN Utils!TransitionToUnattached(m.mepoch)
                           ELSE Utils!NoTransition(i)
               logOk == Utils!CompareEntries(m.mlastLogOffset,
                                             m.mlastLogEpoch,
                                             Len(log[i]),
                                             Utils!LastEpoch(log[i])) >= 0
               grant == /\ \/ state0.state = Unattached
                           \/ /\ state0.state = Voted
                              /\ votedFor[i] = j
                        /\ logOk
               finalState == IF grant /\ state0.state = Unattached
                             THEN Utils!TransitionToVoted(i, m.mepoch, state0)
                             ELSE state0
            IN /\ IF error = Nil
                  THEN
                       /\ state' = [state EXCEPT ![i] = finalState.state]
                       /\ currentEpoch' = [currentEpoch EXCEPT ![i] = finalState.epoch]
                       /\ leader' = [leader EXCEPT ![i] = finalState.leader]
                       /\ \/ /\ grant
                             /\ votedFor' = [votedFor EXCEPT ![i] = j]
                          \/ /\ ~grant
                             /\ UNCHANGED votedFor
                       /\ IF state # state'
                          THEN pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
                          ELSE UNCHANGED pendingFetch
                       /\ Utils!Reply([mtype   |-> RequestVoteResponse,
                                 mepoch        |-> m.mepoch,
                                 mleader       |-> finalState.leader,
                                 mvoteGranted  |-> grant,
                                 merror        |-> Nil,
                                 msource       |-> i,
                                 mdest         |-> j], m)
                  ELSE /\ Utils!Reply([mtype   |-> RequestVoteResponse,
                                 mepoch        |-> currentEpoch[i],
                                 mleader       |-> leader[i],
                                 mvoteGranted  |-> FALSE,
                                 merror        |-> error,
                                 msource       |-> i,
                                 mdest         |-> j], m)
                       /\ UNCHANGED <<serverVars>>
               /\ UNCHANGED <<candidateVars, leaderVars, logVars, auxVars>>

\* Server i receives a RequestVote response from server j.
\* If the response is stale the server i will not register the vote either way.
HandleRequestVoteResponse ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, RequestVoteResponse, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               newState == Utils!MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN
              /\ IF newState.handled = TRUE
                 THEN /\ state' = [state EXCEPT ![i] = newState.state]
                      /\ leader' = [leader EXCEPT ![i] = newState.leader]
                      /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
                      /\ UNCHANGED <<votesGranted>>
                 ELSE
                      /\ state[i] = Candidate
                      /\ \/ /\ m.mvoteGranted
                            /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                      votesGranted[i] \cup {j}]
                         \/ /\ ~m.mvoteGranted
                            /\ UNCHANGED <<votesGranted>>
                      /\ UNCHANGED <<state, leader, currentEpoch>>
              /\ Utils!Discard(m)
              /\ UNCHANGED <<votedFor, pendingFetch, leaderVars, logVars, auxVars>>

\* Candidate i transitions to leader and notifies all peers of its leadership via the BeginQuorumRequest.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'  = [state EXCEPT ![i] = Leader]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ endOffset' = [endOffset EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ Utils!SendMultipleOnce(
          {[mtype    |-> BeginQuorumRequest,
            mepoch   |-> currentEpoch[i],
            msource  |-> i,
            mdest    |-> j] : j \in Servers \ {i}})
    /\ UNCHANGED <<currentEpoch, votedFor, pendingFetch, candidateVars, auxVars, logVars>>

\* A server receives a BeginQuorumRequest and transitions to a follower unless the message is stale.
HandleBeginQuorumRequest ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, BeginQuorumRequest, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               error    == IF m.mepoch < currentEpoch[i]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               newState == Utils!MaybeTransition(i, m.msource, m.mepoch)
           IN IF error = Nil
              THEN
                   /\ state' = [state EXCEPT ![i] = newState.state]
                   /\ leader' = [leader EXCEPT ![i] = newState.leader]
                   /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
                   /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
                   /\ Utils!Reply([mtype |-> BeginQuorumResponse,
                             mepoch      |-> m.mepoch,
                             msource     |-> i,
                             mdest       |-> j,
                             merror      |-> Nil], m)
              ELSE /\ Utils!Reply([mtype |-> BeginQuorumResponse,
                             mepoch      |-> currentEpoch[i],
                             msource     |-> i,
                             mdest       |-> j,
                             merror      |-> error], m)
                   /\ UNCHANGED <<state, leader, currentEpoch, pendingFetch>>
        /\ UNCHANGED <<votedFor, log, candidateVars, leaderVars, highWatermark, auxVars>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ acked[v] = Nil \* prevent submitting the same value repeatedly
    /\ LET entry == [epoch |-> currentEpoch[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           /\ acked' = [acked EXCEPT ![v] = FALSE]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, highWatermark, electionCtr, restartCtr>>

\* Follower i sends leader j a FetchRequest.
SendFetchRequest(i, j) ==
    /\ i # j
    /\ state[i] = Follower
    /\ leader[i] = j
    /\ pendingFetch[i] = Nil
    /\ LET lastLogOffset == Len(log[i])
           lastLogEpoch == IF lastLogOffset > 0
                           THEN log[i][lastLogOffset].epoch
                           ELSE 0
           fetchMsg     == [mtype             |-> FetchRequest,
                            mepoch            |-> currentEpoch[i],
                            mfetchOffset      |-> lastLogOffset,
                            mlastFetchedEpoch |-> lastLogEpoch,
                            msource           |-> i,
                            mdest             |-> j]
       IN /\ pendingFetch' = [pendingFetch EXCEPT ![i] = fetchMsg]
          /\ Utils!Send(fetchMsg)
    /\ UNCHANGED <<currentEpoch, state, votedFor, leader, candidateVars, leaderVars, logVars, auxVars>>

\* Server i rejects a FetchRequest due to either:
\* - i is not a leader
\* - the message epoch is lower than the server epoch
\* - the message epoch is higher than the server epoch
RejectFetchRequest ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, FetchRequest, AnyEpoch)
        /\ LET i                   == m.mdest
               j                   == m.msource
               error               == CASE state[i] # Leader -> NotLeader
                                        [] m.mepoch < currentEpoch[i] -> FencedLeaderEpoch
                                        [] m.mepoch > currentEpoch[i] -> UnknownLeader
                                        [] OTHER -> Nil
           IN  /\ error # Nil
               /\ Utils!Reply([mtype |-> FetchResponse,
                         mresult     |-> NotOk,
                         merror      |-> error,
                         mleader     |-> leader[i],
                         mepoch      |-> currentEpoch[i],
                         mhwm        |-> highWatermark[i],
                         msource     |-> i,
                         mdest       |-> j,
                         correlation |-> m], m)
               /\ UNCHANGED <<candidateVars, leaderVars, serverVars, logVars, auxVars>>

\* Leader i receives a FetchRequest from an inconsistent log position so it responds with the highest
\* offset that matches the epoch of the follower fetch position so it can truncate its log and start
\* fetching from a consistent offset.
DivergingFetchRequest ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ LET i                   == m.mdest
               j                   == m.msource
               valid               == Utils!ValidFetchPosition(i, m)
               validOffsetAndEpoch == Utils!EndOffsetForEpoch(i, m.mlastFetchedEpoch)
           IN  /\ state[i] = Leader
               /\ ~valid
               /\ Utils!Reply([mtype         |-> FetchResponse,
                         mepoch              |-> currentEpoch[i],
                         mresult             |-> Diverging,
                         merror              |-> Nil,
                         mdivergingEpoch     |-> validOffsetAndEpoch.epoch,
                         mdivergingEndOffset |-> validOffsetAndEpoch.offset,
                         mleader             |-> leader[i],
                         mhwm                |-> highWatermark[i],
                         msource             |-> i,
                         mdest               |-> j,
                         correlation         |-> m], m)
               /\ UNCHANGED <<candidateVars, leaderVars, serverVars, logVars, auxVars>>

\* Leader i receives a FetchRequest from a valid position and responds with an entry if there is one
\* or an empty response if not. The leader updates the end offset of the fetching peer and advances the
\* high watermark if it can. It can only advance the high watermark to an entry of the current epoch.
NewHighwaterMark(i, newEndOffset) ==
    LET Agree(offset) == {i} \cup {k \in Servers :
                            /\ newEndOffset[k] >= offset }
        \* the maximum offsets for which a quorum agrees
        agreeOffsets  == {offset \in 1..Len(log[i]) :
                            Agree(offset) \in Quorum}
    IN
        IF /\ agreeOffsets # {}
           /\ log[i][Utils!Max(agreeOffsets)].epoch = currentEpoch[i]
        THEN
            Utils!Max(agreeOffsets)
        ELSE
            highWatermark[i]

\* Server i is a leader and accepts a FetchRequest.
AcceptFetchRequest ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ LET i       == m.mdest
               j       == m.msource
               valid   == Utils!ValidFetchPosition(i, m)
               offset  == m.mfetchOffset + 1
               entries == IF offset > Len(log[i])
                          THEN <<>>
                          ELSE <<log[i][offset]>>
           IN
              /\ state[i] = Leader
              /\ valid
              /\ LET newEndOffset == [endOffset[i] EXCEPT ![j] = m.mfetchOffset]
                     newHwm == NewHighwaterMark(i, newEndOffset)
                 IN
                    /\ endOffset' = [endOffset EXCEPT ![i] = newEndOffset]
                    /\ highWatermark' = [highWatermark EXCEPT ![i] = newHwm]
                    /\ acked' = [v \in Values |->
                                    IF acked[v] = FALSE
                                    THEN v \in { log[i][ind].value : ind \in highWatermark[i]+1..newHwm }
                                    ELSE acked[v]]
                    /\ Utils!Reply([mtype |-> FetchResponse,
                              mepoch      |-> currentEpoch[i],
                              mleader     |-> leader[i],
                              mresult     |-> Ok,
                              merror      |-> Nil,
                              mentries    |-> entries,
                              mhwm        |-> Utils!Min({newHwm, offset}),
                              msource     |-> i,
                              mdest       |-> j,
                              correlation |-> m], m)
                    /\ UNCHANGED <<candidateVars, currentEpoch, log, state, votedFor,
                                   pendingFetch, leader, electionCtr, restartCtr>>

\* Follower i receives a valid Fetch response from server j and appends any entries
\* to its log and updates its high watermark.
HandleSuccessFetchResponse ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ LET i     == m.mdest
               j     == m.msource
               newState == Utils!MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN /\ newState.handled = FALSE
              /\ pendingFetch[i] = m.correlation
              /\ m.mresult = Ok
              /\ highWatermark'  = [highWatermark  EXCEPT ![i] = m.mhwm]
              /\ IF Len(m.mentries) > 0
                 THEN log' = [log EXCEPT ![i] = Append(@, m.mentries[1])]
                 ELSE UNCHANGED log
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
              /\ Utils!Discard(m)
              /\ UNCHANGED <<currentEpoch, state, leader, votedFor, candidateVars, endOffset, auxVars>>

\* Follower i receives a Fetch response from server j and the response indicates that the fetch position
\* is inconsistent. The response includes the highest offset of the last common epoch the leader and follower
\* share, so the follower truncates its log to the highest entry it has at or below that point which will be
\* the highest common entry that the leader and follower share. After this it can send another FetchRequest
\* to the leader from a valid fetch position.
HandleDivergingFetchResponse ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               newState == Utils!MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN
              /\ newState.handled = FALSE
              /\ pendingFetch[i] = m.correlation
              /\ m.mresult = Diverging
              /\ log' = [log EXCEPT ![i] = Utils!TruncateLog(i, m)]
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
              /\ Utils!Discard(m)
        /\ UNCHANGED <<currentEpoch, state, leader, votedFor, candidateVars, leaderVars,
                       highWatermark, auxVars>>

\* Server i receives a FetchResponse with an error from server j.
\* Depending on the error, the follower may transition to being unattached
\* or being the follower of a new leader that it was no aware of.
HandleErrorFetchResponse ==
    \E m \in DOMAIN messages :
        /\ Utils!ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               newState == Utils!MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN
              /\ newState.handled = TRUE
              /\ pendingFetch[i] = m.correlation
              /\ state' = [state EXCEPT ![i] = newState.state]
              /\ leader' = [leader EXCEPT ![i] = newState.leader]
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
              /\ Utils!Discard(m)
        /\ UNCHANGED <<votedFor, candidateVars, leaderVars, logVars, auxVars>>

----

Next ==
    \/ \E i \in Servers : Restart(i)
    \* elections
    \/ \E i \in Servers : RequestVote(i)
    \/ HandleRequestVoteRequest
    \/ HandleRequestVoteResponse
    \/ \E i \in Servers : BecomeLeader(i)
    \* leader actions
    \/ \E i \in Servers, v \in Values : ClientRequest(i, v)
    \/ RejectFetchRequest
    \/ DivergingFetchRequest
    \/ AcceptFetchRequest
    \* follower actions
    \/ HandleBeginQuorumRequest
    \/ \E i,j \in Servers : SendFetchRequest(i, j)
    \/ HandleSuccessFetchResponse
    \/ HandleDivergingFetchResponse
    \/ HandleErrorFetchResponse
    \*\/ \E m \in DOMAIN messages : Utils!DuplicateMessage(m)
    \*\/ \E m \in DOMAIN messages : Utils!DropMessage(m)

Spec == Init /\ [][Next]_vars

----

\* INVARIANT: If a server enters an illegal state then something went wrong.
\* An IllegalState should not be possible.
NoIllegalState ==
    ~\E i \in Servers :
        state[i] = IllegalState

\* INVARIANT: Each log offset is consistent across all servers (on those
\* servers whose highWatermark is equal or higher than the offset).
NoLogDivergence ==
    \A s1, s2 \in Servers :
        IF s1 = s2
        THEN TRUE
        ELSE
            LET lowestCommonHWM == Utils!MinHighWatermark(s1, s2)
            IN IF lowestCommonHWM > 0
               THEN \A offset \in 1..lowestCommonHWM : log[s1][offset] = log[s2][offset]
               ELSE TRUE

\* INVARIANT: We cannot have two servers having a conflicting
\* view on who the leader is in the same epoch.
NeverTwoLeadersInSameEpoch ==
    ~\E i, j \in Servers :
        /\ leader[i] # Nil
        /\ leader[j] # Nil
        /\ leader[i] # leader[j]
        /\ currentEpoch[i] = currentEpoch[j]

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
                    /\ currentEpoch[l] > currentEpoch[i]
                \* and that is missing the value
                /\ ~\E offset \in DOMAIN log[i] :
                    log[i][offset].value = v
        ELSE TRUE

\* INVARIANT: There cannot be a committed entry that is not at majority quorum
\* Don't use this invariant when allowing data loss on a server.
CommittedEntriesReachMajority ==
    IF \E i \in Servers : state[i] = Leader /\ highWatermark[i] > 0
    THEN \E i \in Servers :
           /\ state[i] = Leader
           /\ highWatermark[i] > 0
           /\ \E quorum \in SUBSET Servers :
               /\ Cardinality(quorum) = (Cardinality(Servers) \div 2) + 1
               /\ i \in quorum
               /\ \A j \in quorum :
                   /\ Len(log[j]) >= highWatermark[i]
                   /\ log[j][highWatermark[i]] = log[i][highWatermark[i]]
    ELSE TRUE

\* LIVENESS: A client value will either get committed and be fully replicated
\* or it will be truncated and not be found on any server log. Note that due to
\* the number of elections being limited, the last possible election could fail
\* and prevent progress, so this liveness formula only apples in cases a behaviour
\* does not end with all elections used up and no elected leader. Additionally,
\* you cannot use symmetry sets if the set is used in a liveness property.
ValuesNotStuck ==
    \A v \in Values : []<>Utils!ValueAllOrNothing(v)

====
