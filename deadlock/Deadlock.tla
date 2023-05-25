(*
A blocking queue is a buffer that holds the data created by producing threads until they are retrieved by consuming threads.
More importantly, the buffer acts as a synchronizer, blocking and suspending threads when there is nothing for them to do.
The buffer has finite capacity, producing threads must be suspended when the buffer is full.
Any consuming thread needs to be blocked until there is data in the buffer.

When Get calls Notify, the intent is to notify a producer that a slot has been made available in the buffer,
but this call can sometimes notify a consumer instead and, if this happens a few times, it can lead to a deadlock.
The Java reproducer may take a lot of time without gitving a clear error trace (logs are interleaved).
*)
---- MODULE Deadlock ----

EXTENDS Naturals, Sequences

CONSTANTS
    Producers, \* Set of producers.
    Consumers, \* Set of consumers.
    BufCapacity, \* Max amount of messages in the bounded buffer.
    Data \* Set of values that can be produced and/or consumed.

ASSUME
    /\ Producers # {} \* At least one producer.
    /\ Consumers # {} \* At least one consumer.
    /\ Producers \intersect Consumers = {} \* No thread is both producer and consumer.
    /\ BufCapacity > 0 \* Buffer capacity is at least 1.
    /\ Data # {} \* The type of data is nonempty.

VARIABLES
    buffer, \* the buffer (sequence of messages)
    waitSet \* the wait set of threads
vars == <<buffer, waitSet>>

Participants == (Producers \cup Consumers)
RunningThreads == (Producers \cup Consumers) \ waitSet

Init ==
    /\ buffer = <<>> \* The buffer is empty.
    /\ waitSet = {} \* No thread is waiting.

----

Notify ==
    IF waitSet # {}
    THEN \E t \in waitSet : waitSet' = waitSet \ {t}
    ELSE UNCHANGED waitSet

NotifyAll ==
    waitSet' = {}

Wait(t) ==
    waitSet' = waitSet \cup {t}

Put(t, m) ==
    IF Len(buffer) < BufCapacity
    THEN /\ buffer' = Append(buffer, m)
         /\ Notify
    ELSE /\ Wait(t)
         /\ UNCHANGED buffer

Get(t) ==
    IF Len(buffer) > 0
    THEN /\ buffer' = Tail(buffer)
         /\ Notify \* replace Notify with NotifyAll to fix it
    ELSE /\ Wait(t)
         /\ UNCHANGED buffer

RunThread(t) ==
    \/ /\ t \in Producers
       /\ \E m \in Data : Put(t, m)
    \/ /\ t \in Consumers
       /\ Get(t)

\* Pick a thread out of all running threads and have it do its thing.
Next == \E t \in RunningThreads : RunThread(t)

Spec == Init /\ [][Next]_vars

----

\* INVARIANT: type correctness.
TypeOK ==
    /\ buffer \in Seq(Data)
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitSet \in SUBSET Participants

\* LIVENESS: At least one thread is expectd to run at any time.
NoDeadlock ==
    [](RunningThreads # {})

====
