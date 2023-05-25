(*
LinearizableMemory implements MemoryInterface.
A processor p issues a memory request and then waits for a response before issuing the next request.
The request is executed by accessing (reading or writing) a variable mem.
We let the access of mem occur any time between the request and the response (linearizable memory).
*)
---- MODULE LinearizableMemory ----

EXTENDS MemoryInterface, TLC

VARIABLES
    ctl, \* record containing the request status for each p
    buf, \* record containing either request or response for each p
    mem  \* record containing the memory value for each p
vars == <<ctl, buf, mem, memInt>>

\* We have to tell TLC how to evaluate the operators Send, Reply and initialize InitMemInt.
MCSend(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

\* Used to restrict the state space by skipping symmetrics states.
\* The set must not be used in CHOOSE or liveness expressions.
symmProcAdr == Permutations(Proc) \cup Permutations(Adr)

Init ==
    /\ ctl = [p \in Proc |-> "ready"] \* each processor is ready to issue requests
    /\ buf = [p \in Proc |-> NoVal]   \* each buf[p] is arbitrarily initialized to NoVal
    /\ mem \in [Adr -> Val]           \* memory locations have any values in Val
    /\ memInt \in InitMemInt          \* memInt is any element of InitMemInt

----

Req(p) ==
    /\ ctl[p] = "ready"                      \* enabled if p is ready to issue a request
    /\ \E req \in MReq :                     \* for some request req
        /\ Send(p, req, memInt, memInt')     \* send req on the interface
        /\ ctl' = [ctl EXCEPT ![p] = "busy"] \* set ctl[p] to busy
        /\ buf' = [buf EXCEPT ![p] = req]    \* set buf[p] to the request
    /\ UNCHANGED mem

Do(p) ==
    /\ ctl[p] = "busy"                                     \* enabled if p request is pending
    /\ mem' = IF buf[p].op = "write"
              THEN [mem EXCEPT ![buf[p].adr] = buf[p].val] \* write: write to memory
              ELSE mem                                     \* read: leave memory unchanged
    /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "write"
                                 THEN NoVal                \* write: set buf[p] to NoVal
                                 ELSE mem[buf[p].adr]]     \* read: set the memory value
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED memInt

Rsp(p) ==
    /\ ctl[p] = "done"                    \* enabled if req done but resp not sent
    /\ Reply(p, buf[p], memInt, memInt')  \* send the response on the interface
    /\ ctl' = [ctl EXCEPT ![p] = "ready"] \* set ctl[p] to ready
    /\ UNCHANGED <<mem, buf>>

----

Next == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

Fairness == \A p \in Proc : WF_vars(Do(p) \/ Rsp(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----

\* INVARIANT: Type correctness.
TypeOK ==
    /\ mem \in [Adr -> Val]                          \* mem is a function from Adr to Val
    /\ ctl \in [Proc -> {"ready", "busy", "done"}]   \* ctl is equal ready, busy or done
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]  \* buf[p] is a request or a response

====
