(*
A memory system consists of a set of processors connected to a memory by some abstract interface, which we label memInt.
It's a Send step if a processor is sending the value to the memory, and a Reply step if the memory is sending to a processor.
Processors do not send values to one another, and the memory sends to only one processor at a time.
*)
---- MODULE MemoryInterface ----

\* We leave Send and Reply unspecified by making them parameters.
CONSTANTS
    Send(_,_,_,_),  \* processor p sending value d to the memory
    Reply(_,_,_,_), \* memory sending value d to processor p
    InitMemInt,     \* set of possible initial values of memInt
    Proc,           \* set of processor identifiers
    Adr,            \* set of memory addresses
    Val             \* set of memory values

VARIABLES memInt \* current state of the memory

\* Set of all request records.
MReq == [op:{"read"}, adr:Adr] \cup [op:{"write"}, adr:Adr, val:Val]

\* Arbitrary value not in Val.
NoVal == CHOOSE v : v \notin Val

====
