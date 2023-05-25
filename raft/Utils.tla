---- MODULE Utils ----

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Servers
CONSTANTS Values
CONSTANTS Follower, Candidate, Leader
CONSTANTS Nil
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse
CONSTANTS EqualTerm, LessOrEqualTerm
CONSTANTS MaxElections, MaxRestarts

VARIABLES messages
VARIABLES currentTerm
VARIABLES state
VARIABLES votedFor
serverVars == <<currentTerm, state, votedFor>>
VARIABLES log
VARIABLES commitIndex
logVars == <<log, commitIndex>>
VARIABLES votesGranted
candidateVars == <<votesGranted>>
VARIABLES nextIndex
VARIABLES matchIndex
VARIABLES pendingResponse
leaderVars == <<nextIndex, matchIndex, pendingResponse>>
VARIABLES acked
VARIABLES electionCtr, restartCtr
auxVars == <<acked, electionCtr, restartCtr>>

----

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Send the message whether it already exists or not.
SendNoRestriction(m) ==
    IF m \in DOMAIN messages
    THEN messages' = [messages EXCEPT ![m] = @ + 1]
    ELSE messages' = messages @@ (m :> 1)

\* Will only send the message if it hasn't been sent before.
\* Basically disables the parent action once sent.
SendOnce(m) ==
    /\ m \notin DOMAIN messages
    /\ messages' = messages @@ (m :> 1)

\* Add a message to the bag of messages.
\* Note 1: to prevent infinite cycles, empty AppendEntriesRequest messages can only be sent once.
\* Note 2: a message can only match an existing message if it is identical (all fields).
Send(m) ==
    IF /\ m.mtype = AppendEntriesRequest
       /\ m.mentries = <<>>
    THEN SendOnce(m)
    ELSE SendNoRestriction(m)

\* Will only send the messages if it hasn't done so before.
\* Basically disables the parent action once sent.
SendMultipleOnce(msgs) ==
    /\ \A m \in msgs : m \notin DOMAIN messages
    /\ messages' = messages @@ [msg \in msgs |-> 1]

\* Explicit duplicate operator for when we purposefully want message duplication.
Duplicate(m) ==
    /\ m \in DOMAIN messages
    /\ messages' = [messages EXCEPT ![m] = @ + 1]

\* Remove a message from the bag of messages. Used when a server is done processing a message.
Discard(m) ==
    /\ m \in DOMAIN messages
    /\ messages[m] > 0 \* message must exist
    /\ messages' = [messages EXCEPT ![m] = @ - 1]

\* Combination of Send and Discard.
Reply(response, request) ==
    /\ messages[request] > 0 \* request must exist
    /\ \/ /\ response \notin DOMAIN messages \* response does not exist, so add it
          /\ messages' = [messages EXCEPT ![request] = @ - 1] @@ (response :> 1)
       \/ /\ response \in DOMAIN messages \* response was sent previously, so increment delivery counter
          /\ messages' = [messages EXCEPT ![request] = @ - 1,
                                          ![response] = @ + 1]

\* The message is of the type and has a matching term.
\* Messages with a higher term are handled by the action UpdateTerm.
ReceivableMessage(m, mtype, termMatch) ==
    /\ messages[m] > 0
    /\ m.mtype = mtype
    /\ \/ /\ termMatch = EqualTerm
          /\ m.mterm = currentTerm[m.mdest]
       \/ /\ termMatch = LessOrEqualTerm
          /\ m.mterm <= currentTerm[m.mdest]

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Checks if message m is compatible with the log of server i.
LogOk(i, m) ==
    \/ m.mprevLogIndex = 0
    \/ /\ m.mprevLogIndex > 0
       /\ m.mprevLogIndex <= Len(log[i])
       /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term

\* Checks if the message previous log index is what is expected.
CanAppend(m, i) ==
    /\ m.mentries # <<>>
    /\ Len(log[i]) = m.mprevLogIndex

\* Truncate in two cases:
\* - the last log entry index is >= than the entry being received
\* - this is an empty RPC and the last log entry index is > than the previous log entry received
NeedsTruncation(m, i, index) ==
    \/ /\ m.mentries # <<>>
       /\ Len(log[i]) >= index
    \/ /\ m.mentries = <<>>
       /\ Len(log[i]) > m.mprevLogIndex

\* Truncate the log.
TruncateLog(m, i) ==
    [index \in 1..m.mprevLogIndex |-> log[i][index]]

\* The network duplicates a message.
\* There is no state-space control for this action, it causes infinite state space.
DuplicateMessage(m) ==
    /\ Duplicate(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, auxVars>>

\* The network drops a message.
\* The specification does not force any server to receive a message, so we already get this for free.
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, auxVars>>

MinCommitIndex(s1, s2) ==
    IF commitIndex[s1] < commitIndex[s2]
    THEN commitIndex[s1]
    ELSE commitIndex[s2]

ValueInServerLog(i, v) == \E index \in DOMAIN log[i] : log[i][index].value = v

ValueAllOrNothing(v) ==
    IF /\ electionCtr = MaxElections
       /\ ~\E i \in Servers : state[i] = Leader
    THEN TRUE
    ELSE \/ \A i \in Servers : ValueInServerLog(i, v)
         \/ ~\E i \in Servers : ValueInServerLog(i, v)

====
