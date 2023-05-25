(*
The Two-Phase Commit protocol (2PC) is an implementation/refinement of the TCommit.
that uses a Transaction Manager process (TM) to coordinate the decision making procedure.
This protocol blocks if the TM fails (see Raft for a non-blocking consesus algorithm).
In this specification, we ignore Prepared messages sent by the TM (RMs spontaneously issue them).
We eliminate Abort messages sent by an RM when it decides to abort.
*)
---- MODULE TwoPhase ----

EXTENDS TLC

CONSTANTS RM \* set of resource managers

VARIABLES
    rmState,    \* rmState[r] is the state of resource manager r.
    tmState,    \* state of the transaction manager.
    tmPrepared, \* set of RMs from which the TM has received Prepared messages.
    msgs        \* set of all messages ever sent (no need to remove them when received)
vars == <<rmState, tmState, tmPrepared, msgs>>

\* Set of all possible messages (Prepared from RM to TM, Commit/Abort from TM to all RMs).
Messages == [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]

\* Used to restrict the state space by skipping symmetrics states.
\* The set must not be used in CHOOSE or liveness expressions.
symmRM == Permutations(RM)

Init ==
    /\ rmState = [r \in RM |-> "working"]
    /\ tmState = "init"
    /\ tmPrepared   = {}
    /\ msgs = {}

----

\* TM receives a Prepared message from RM r.
TMRcvPrepared(r) ==
    /\ tmState = "init"
    /\ [type |-> "Prepared", rm |-> r] \in msgs
    /\ tmPrepared' = tmPrepared \cup {r}
    /\ UNCHANGED <<rmState, tmState, msgs>>

\* TM commits the transaction.
TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

\* TM spontaneously aborts the transaction.
TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

\* RM r prepares.
RMPrepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
    /\ UNCHANGED <<tmState, tmPrepared>>

\* RM r spontaneously decides to abort.
RMChooseToAbort(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* RM r is told by the TM to commit.
RMRcvCommitMsg(r) ==
    /\ [type |-> "Commit"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* RM r is told by the TM to abort.
RMRcvAbortMsg(r) ==
    /\ [type |-> "Abort"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

----

Next ==
    \/ TMCommit \/ TMAbort
    \/ \E r \in RM :
        TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
            \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)

Spec == Init /\ [][Next]_vars

----

\* INVARIANT: Type correctness.
TypeOK ==
    /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    /\ tmState \in {"init", "done"}
    /\ tmPrepared \subseteq RM
    /\ msgs \subseteq Messages

====
