(*
WriteThroughCache implements MemoryInterface and instantiate LinearizableMemory.

Each processor p communicates with a local controller, which maintains three state components.
The value of cache[p] represents the processor's cache.
Requests from the processors to the main memory are in the queue memQ of maximum length QLen.

Every write request updates the main memory.
The DoWr(p) action writes the value into cache[p] and adds the write request to the tail of memQ.
It also updates cache[q] for every other processor q that has a copy of the address in its cache.
When the request reaches the head of memQ, the action MemQWr stores the value in wmem.

A read request by processor p is performed by the action DoRd(p), which obtains the value from cache.
If the value is not in the cache, the action RdMiss(p) adds the request to the tail of memQ and sets ctl[p] to waiting.
When the request reaches the head of memQ, the action MemQRd reads the value and puts it in cache[p], enabling DoRd(p).
MemQRd must read the value from the last write to that address in memQ, if there is such a write, otherwise from wmem.
*)
---- MODULE WriteThroughCache ----

EXTENDS Naturals, Sequences, MemoryInterface, TLC

CONSTANTS QLen \* memQ length.

VARIABLES
    wmem, ctl, buf,
    cache, \* cache[p][a] is the value in p's cache for address a
    memQ   \* sequence of pairs (p, req)
vars == <<memInt, wmem, ctl, buf, cache, memQ>>

\* Instance of LinearizableMemory.
M == INSTANCE LinearizableMemory WITH mem <- wmem

\* We need to tell TLC model checker the values of Send, Reply and InitMemInt.
MCSend(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

\* Used to restrict the state space by skipping symmetrics states.
\* The set must not be used in CHOOSE or liveness expressions.
symmProcAdr == Permutations(Proc) \cup Permutations(Adr)

Init ==
    /\ M!Init
    /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]] \* all caches empty
    /\ memQ = <<>>                                    \* memQ empty

----

\* Processor p issues a request.
Req(p) == M!Req(p) /\ UNCHANGED <<cache, memQ>>

\* The system issues a response to processor p.
Rsp(p) == M!Rsp(p) /\ UNCHANGED <<cache, memQ>>

\* Enqueue a request to write value from memory to p's cache.
RdMiss(p) ==
    /\ (ctl[p] = "busy") /\ (buf[p].op = "read") \* enabled on read requests when
    /\ cache[p][buf[p].adr] = NoVal              \* the address is not in p's cache
    /\ Len(memQ) < QLen                          \* and memQ is not full
    /\ memQ' = Append(memQ, <<p, buf[p]>>)       \* append (p, req) to memQ
    /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<memInt, wmem, buf, cache>>

\* Perform a read by p of a value in its cache.
DoRd(p) ==
    /\ ctl[p] \in {"busy", "waiting"}                  \* enabled if it is a pending
    /\ buf[p].op = "read"                              \* read request and
    /\ cache[p][buf[p].adr] # NoVal                    \* address is in cache
    /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]] \* get result from cache
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED <<memInt, wmem, cache, memQ>>

\* Write to p's cache, update other caches, and enqueue memory update.
DoWr(p) ==
    LET r == buf[p] \* processor p's request
    IN /\ (ctl[p] = "busy") /\ (r.op = "write") \* enabled if write request pending
       /\ Len(memQ) < QLen                      \* and memQ is not full
       /\ cache' = \* update p's cache and any other cache that has a copy
           [q \in Proc |-> IF (p = q) \/ (cache[q][r.adr] # NoVal)
                           THEN [cache[q] EXCEPT ![r.adr] = r.val]
                           ELSE cache[q]]
       /\ memQ' = Append(memQ, <<p, r>>)   \* enqueue write at tail of memQ
       /\ buf' = [buf EXCEPT ![p] = NoVal] \* generate response
       /\ ctl' = [ctl EXCEPT ![p] = "done"]
       /\ UNCHANGED <<memInt, wmem>>

\* Recursive function to get the value wmem will have after all the writes in memQ.
vmem ==
    LET f[i \in 0..Len(memQ)] ==
        IF i = 0 THEN wmem
                 ELSE LET r == memQ[i][2] \* Queued request.
                      IN IF memQ[i][2].op = "read"
                         THEN f[i - 1]
                         ELSE [f[i - 1] EXCEPT ![r.adr] = r.val]
    IN f[Len(memQ)]

\* Perform an enqueued read to memory.
MemQRd ==
    LET p == Head(memQ)[1] \* requesting processor
        r == Head(memQ)[2] \* request at the head of memQ
    IN /\ (memQ # <<>>) /\ (r.op = "read")                  \* enabled if head of memQ is a read
       /\ memQ' = Tail(memQ)                                \* remove the head of memQ
       /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]] \* put value from memory or memQ in p's cache
       /\ UNCHANGED <<memInt, wmem, buf , ctl>>

\* Perform write at the head of memQ to memory.
MemQWr ==
    LET r == Head(memQ)[2] \* request at the head of memQ.
    IN /\ (memQ # <<>>) /\ (r.op = "write")      \* enabled if head of memQ is a write
       /\ wmem' = [wmem EXCEPT ![r.adr] = r.val] \* perform the write to memory
       /\ memQ' = Tail(memQ)                     \* remove the write from memQ
       /\ UNCHANGED <<memInt, buf , ctl , cache>>

\* Remove address a from p's cache.
Evict(p, a) ==
    /\ (ctl[p] = "waiting") => (buf[p].adr # a) \* can't evict, just written to satisfy a pending read
    /\ cache' =  [cache EXCEPT ![p][a] = NoVal]
    /\ UNCHANGED <<memInt, wmem, buf , ctl, memQ>>

Next ==
    \/ \E p \in Proc : \/ Req(p) \/ Rsp(p)
                       \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
                       \/ \E a \in Adr : Evict(p, a)
    \/ MemQWr \/ MemQRd

\* Every request eventually receives a response.
\* RdMiss(p) and DoWr(p) require SF becasue they are disabled before execution when memQ is full.
Fairness ==
    /\ \A p \in Proc : /\ WF_vars(Rsp(p) \/ DoRd(p))
                       /\ SF_vars(RdMiss(p) \/ DoWr(p))
    /\ WF_vars(MemQWr \/ MemQRd)

Spec == Init /\ [][Next]_vars /\ Fairness

----

\* INVARIANT: Type correctness.
TypeOK ==
    /\ wmem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"ready", "busy", "waiting", "done"}]
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
    /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
    /\ memQ \in Seq(Proc \X MReq) \* memQ is a sequence of (proc, request) pairs

\* INVARIANT: Predicate asserting that if two processors' caches have
\* copies of an address, then those copies have equal values.
Coherence ==
    \A p, q \in Proc, a \in Adr :
        (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

====
