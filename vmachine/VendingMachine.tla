(*
Simple vending machine.

A TLA+ (Temporal Logic of Actions) is a formal specification language that can be used to create a mathematical model of a system.
The TLC model checker tool can be use to verify design correctness, and it is particularly effective at revealing concurrency errors.
TLC has a collection of worker threads that compute the graph of reachable states and check safety and liveness properties.
If one doesn't, it will return an error trace (counter example) showing how to reproduce the bad behavior (sequence of states).
If the output statistics include an action that was never enabled, then there is something wrong.

The properties check works by doing a multi-threaded breadth-first search of the state graph (aka state space).
Due to this brute force approach, the input parameters size must be limited to avoid the state space explosion.
If the state space is too big or infinite, we can restrict to a reasonable subset of it (patience and RAM set the limit).
This means a model will not always guarantee correctness, but empirically most errors appear with a small state space.

Safety means bad things never happen, while liveness means good things eventually happen.
An invariant is specific type of safety property that must be true on every single state.
Instead, temporal properties are checked against two consecutive states (safety) or the entire behavior (liveness).
Invariants are useful to catch errors, but they don't tell if the system is making progress or is stuck, this is where liveness properties help.
*)
---- MODULE VendingMachine ----

EXTENDS Naturals

\* Runtime parameters.
CONSTANTS Max \* max number of cans
\* Constants' validation (checked before the model runs).
ASSUME Max > 0

\* Global variables.
VARIABLES
    coke,   \* available cans of coke
    sprite, \* available cans of sprite
    coin,   \* wether a coin was entered
    wallet  \* earnings since last refill
vars == <<coke, sprite, coin, wallet>>

\* Initial state formula (possible initial values of variables).
Init ==
    /\ coke = Max
    /\ sprite = Max
    /\ coin = 0
    /\ wallet = 0

----

\* State transition formulas (next-state actions).
GetCoke ==
    /\ coin > 0
    /\ coke > 0 \* enablement condition
    /\ coin' = coin - 1 \* state change
    /\ wallet' = wallet + 1
    /\ coke' = coke - 1
    /\ UNCHANGED sprite

GetSprite ==
    /\ coin > 0
    /\ sprite > 0
    /\ coin' = coin - 1
    /\ wallet' = wallet + 1
    /\ sprite' = sprite - 1
    /\ UNCHANGED coke

InsertCoin ==
    /\ coin < coke + sprite
    /\ coin' = coin + 1
    /\ UNCHANGED <<coke, sprite, wallet>>

Refill ==
    /\ coin = 0
    /\ coke = 0
    /\ sprite = 0
    /\ wallet' = 0
    /\ coke' = Max
    /\ sprite' = Max
    /\ UNCHANGED coin

----

\* Next state relationship (non deterministic).
Next ==
    \/ InsertCoin
    \/ GetCoke
    \/ GetSprite
    \/ Refill

\* Fairness constraints that rule out unwanted behaviors (like infinite stutters).
Fairness ==
    /\ WF_vars(InsertCoin)
    /\ WF_vars(GetCoke)
    /\ WF_vars(GetSprite) \* weak: eventualy happens if always enabled
    /\ SF_vars(Refill) \* strong: eventualy happens if intermittently enabled

\* Temporal formula that describes any possible behavior.
Spec == Init /\ [][Next]_vars /\ Fairness

----

\* INVARIANT: Type correctness (the language is untyped).
TypeOK ==
    /\ coke <= Max
    /\ sprite <= Max
    /\ coin <= coke + sprite
    /\ wallet >= 0

\* INVARIANT: The total number of entered coins is never less than total released cans.
NoFreeDrinks == wallet = (Max - coke) + (Max - sprite)

\* LIVENESS: If we run out of cans, then the machine is eventually refilled.
EventuallyRefill == coke = 0 /\ sprite = 0 ~> coke = Max /\ sprite = Max

====
