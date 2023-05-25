(*
Channel using the alternating bit protocol for communication over an unreliable channel.
Data is sent on val line, and the rdy and ack lines are used for synchronization.
The sender must wait for an ack for one data item before it can send the next.
*)
---- MODULE Channel ----

EXTENDS Naturals

CONSTANTS Data

VARIABLES chan \* record representing a channel

Init ==
    /\ chan \in [val:Data, rdy:{0,1}, ack:{0,1}]
    /\ chan.ack = chan.rdy

----

Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

----

Next == (\E d \in Data : Send(d)) \/ Rcv
Fairness == WF_chan(Rcv)
Spec == Init /\ [][Next]_chan /\ Fairness

----

\* INVARIANT: Type correctness.
TypeOK == chan \in [val:Data, rdy:{0,1}, ack:{0,1}]

\* LIVENESS: Every request must eventually receive a reply.
MustReply == <>(chan.ack = chan.rdy)

====
