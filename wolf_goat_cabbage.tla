A farmer with a wolf, a goat, and a cabbage must cross a river by boat. The boat can carry only 
the farmer and a single item. If left unattended together, the wolf would eat the goat, or the 
goat would eat the cabbage. How can they cross the river without anything being eaten?
https://en.m.wikipedia.org/wiki/Wolf,_goat_and_cabbage_problem

--
This spec tought me the difference between CHOICE and with: 
https://groups.google.com/g/tlaplus/c/QJAulqYgC0E/m/Cm2PPJBDCQAJ
> CHOOSE is definitely a confusing operator, many people have problems with it including myself. 
> The idea is that CHOOSE always picks the same value, it does not represent arbitrary values.
> If you're trying to say "sub can be any element of ClaimsData", then the "there exists" 
> operator (existential quantification) is what you're looking for, i.e.
> \E sub \in ClaimsData: SomePredicate(sub)

And:
> What if multiple values satisfy CHOOSE? In this case the only requirement is that the 
result is deterministic: the engine must always return the same value, no matter what. 
In practice this means that TLC will always choose the lowest value that matches the set.
https://learntla.com/core/operators.html#choose

CHOOSE has to be deterministic but in my previous implementation (in last commit) I was 
trying to use CHOOSE to pick any element in subset of side such that removing that 
item from side would have left it in a valid state.
Because I was using CHOOSE, tlc was always picking the same value leading to a very
small possible state transitions and a lot of headache to me.


---- MODULE wolf_goat_cabbage ----
EXTENDS TLC, FiniteSets, Integers

WOLF == "Wolf"
GOAT == "Goat"
CABBAGE == "Cabbage"
FinalResult == {WOLF, GOAT, CABBAGE}
InvalidStates == {{CABBAGE, GOAT}, {WOLF, GOAT}}
baitinv == TRUE

\*baitinv ==  TLCGet("level") < 14

(* --fair algorithm wolf_goat_cabbage {

variables side_start = FinalResult, side_end = {};

define {
    IsValidState(side) == ~(side \in InvalidStates)
    Inv == side_end # FinalResult
    \* this operator is used to all the possible
    \* subsets of side of cardinality 1 such that
    \* reamoving this subset would leave side in
    \* a valid state.
    ValidSubsets(side) == {s \in SUBSET(side): IsValidState(side_start \ s) /\ Cardinality(s) = 1}
}

macro PickFrom(side, other_side_is_valid) {
    await /\ transport = {} 
            /\ side # {} /\ other_side_is_valid;
    \* choose an item such that this side is left valid:
    with( item \in ValidSubsets(side)) {
        transport := item;
        side := side \ transport;
    }
}

macro DropItemTo(side) {
    \* leave an item to side_start side. If needed to avoid conflicts, load the other item.
    await transport # {};
    side := side \union transport;
    transport := {};
}

fair process (Farmer = 1) 
variable transport = {}; {
W:
    while (TRUE){
        either {
            \* pick an item from side_start and load it.
            PickFrom(side_start, IsValidState(side_end));
        } or {
            \* pick an item from side_start and load it.
            PickFrom(side_end, IsValidState(side_start));
        } or {
            DropItemTo(side_start);
        } or {
            DropItemTo(side_end);
        };
    }
}
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "b19f62f8")
VARIABLES side_start, side_end

(* define statement *)
IsValidState(side) == ~(side \in InvalidStates)
Inv == side_end # FinalResult


ValidSubsets(side) == {s \in SUBSET(side): IsValidState(side_start \ s) /\ Cardinality(s) = 1}

VARIABLE transport

vars == << side_start, side_end, transport >>

ProcSet == {1}

Init == (* Global variables *)
        /\ side_start = FinalResult
        /\ side_end = {}
        (* Process Farmer *)
        /\ transport = {}

Farmer == \/ /\ /\ transport = {}
                  /\ side_start # {} /\ (IsValidState(side_end))
             /\ \E item \in ValidSubsets(side_start):
                  /\ transport' = item
                  /\ side_start' = side_start \ transport'
             /\ UNCHANGED side_end
          \/ /\ /\ transport = {}
                  /\ side_end # {} /\ (IsValidState(side_start))
             /\ \E item \in ValidSubsets(side_end):
                  /\ transport' = item
                  /\ side_end' = side_end \ transport'
             /\ UNCHANGED side_start
          \/ /\ transport # {}
             /\ side_start' = (side_start \union transport)
             /\ transport' = {}
             /\ UNCHANGED side_end
          \/ /\ transport # {}
             /\ side_end' = (side_end \union transport)
             /\ transport' = {}
             /\ UNCHANGED side_start

Next == Farmer

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(Farmer)

\* END TRANSLATION 

TypeOk == /\ \A el \in side_start : el \in {WOLF, GOAT, CABBAGE} 
          /\ \A el \in side_end : el \in {WOLF, GOAT, CABBAGE}
          /\ \A el \in transport : el \in {WOLF, GOAT, CABBAGE}
    

====
