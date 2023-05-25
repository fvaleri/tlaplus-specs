(*
FIFO bounded buffer (bounded queue) for asynchronous communication.
The sender and receiver respectively use in and out channels to communicate with the buffer.
Values are sent over in and out using the asynchronous protocol specified by the Channel module.
*)
---- MODULE FifoBuffer ----

EXTENDS Naturals, Sequences

CONSTANTS
  Message, \* set of messages that can be sent
  N        \* queue capacity

VARIABLES
  in,  \* input channel
  out, \* ouptut channel
  q    \* queue of inflight messages
vars == <<in, out, q>>

\* Instantiation with renaming.
\* Constant/variable substitution is omitted when they have the same name.
InChan == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

Init ==
    /\ InChan!Init
    /\ OutChan!Init
    /\ q = <<>>

----

Send(msg) ==
    /\ InChan!Send(msg) \* send msg on channel in
    /\ UNCHANGED <<out, q>>

BufRcv ==
    /\ Len(q) < N             \* enabled only if q is not full
    /\ InChan!Rcv             \* receive msg from channel in
    /\ q' = Append(q, in.val) \* append msg to tail of q
    /\ UNCHANGED out

BufSend ==
    /\ q # <<>>              \* enabled only if q is not empty
    /\ OutChan!Send(Head(q)) \* send head of q on channel out
    /\ q' = Tail(q)          \* remove head from q
    /\ UNCHANGED in

RRcv ==
    /\ OutChan!Rcv \* receive msg from channel out
    /\ UNCHANGED <<in, q>>

Next ==
    \/ \E msg \in Message : Send(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv

Spec == Init /\ [][Next]_vars

----

\* INVARIANT: Type correctness.
TypeOK ==
    /\ InChan!TypeOK
    /\ OutChan!TypeOK
    /\ q \in Seq(Message) \* set of finite sequences of messages

====
