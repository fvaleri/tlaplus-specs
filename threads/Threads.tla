(*
Model concurrency.
*)
---- MODULE Threads ----

EXTENDS Naturals, Sequences, TLC

CONSTANTS NumThreads, NULL
ASSUME NumThreads > 0

VARIABLES counter, lock
globalVars == <<counter, lock>>

VARIABLES
    tmp, \* sequence hosting thread buffers
    pc   \* record used to emulate thread sequentiality
threadVars == <<tmp, pc>>

vars == <<globalVars, threadVars>>

Threads == 1..NumThreads

Init ==
    /\ counter = 0
    /\ lock = NULL
    /\ tmp = [t \in Threads |-> 0]
    /\ pc = [t \in Threads |-> "GetLock"]

----

\* This is intermittently enabled when lock = NULL.
GetLock(t) ==
    /\ pc[t] = "GetLock"
    /\ lock = NULL
    /\ lock' = t
    /\ pc' = [pc EXCEPT ![t] = "GetCounter"]
    /\ UNCHANGED <<counter, tmp>>

ReleaseLock(t) ==
    /\ pc[t] = "ReleaseLock"
    /\ lock = t
    /\ lock' = NULL
    /\ pc' = [pc EXCEPT ![t] = "Done"]
    /\ UNCHANGED <<counter, tmp>>

GetCounter(t) ==
    /\ pc[t] = "GetCounter"
    /\ tmp' = [tmp EXCEPT ![t] = counter]
    /\ pc' = [pc EXCEPT ![t] = "IncCounter"]
    /\ UNCHANGED <<counter, lock>>

\* Using the tmp sequence we artificially make IncCounter non atomic.
\* Maybe the counter is on a separate machine of the network.
IncCounter(t) ==
    /\ pc[t] = "IncCounter"
    /\ counter' = tmp[t] + 1
    /\ pc' = [pc EXCEPT ![t] = "ReleaseLock"]
    /\ UNCHANGED <<lock, tmp>>

----

RunThread(t) ==
    \/ GetLock(t)
    \/ GetCounter(t)
    \/ IncCounter(t)
    \/ ReleaseLock(t)

\* Allow infinite stuttering to prevent deadlock on termination.
\* Alternatively you can configure: CHECK_DEADLOCK FALSE.
Terminating ==
    /\ \A t \in Threads: pc[t] = "Done"
    /\ UNCHANGED vars

\* With the existential operator we enable concurrency.
Next ==
    \/ \E t \in Threads: RunThread(t)
    \/ Terminating

\* Make every thread fair to avoid starvation.
Fairness == \A t \in Threads : SF_vars(RunThread(t))
Spec == Init /\ [][Next]_vars /\ Fairness

----

CounterNotLtTmp ==
  \A t \in Threads:
    tmp[t] <= counter

\* INVARIANT: Type correctness.
TypeOK ==
    /\ CounterNotLtTmp
    /\ tmp \in [Threads -> 0..NumThreads]
    /\ lock \in Threads \union {NULL}

\* LIVENESS: Eventually, counter is always equal to NumThreads.
Correct ==
    <>[](counter = NumThreads)

====
