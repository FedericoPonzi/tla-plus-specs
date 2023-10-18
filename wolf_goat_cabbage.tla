A farmer with a wolf, a goat, and a cabbage must cross a river by boat. The boat can carry only 
the farmer and a single item. If left unattended together, the wolf would eat the goat, or the 
goat would eat the cabbage. How can they cross the river without anything being eaten?
https://en.m.wikipedia.org/wiki/Wolf,_goat_and_cabbage_problem

---- MODULE wolf_goat_cabbage ----
EXTENDS TLC, FiniteSets, Integers

WOLF == "Wolf"
GOAT == "Goat"
CABBAGE == "Cabbage"
FinalResult == {WOLF, GOAT, CABBAGE}
InvalidStates == {{CABBAGE,GOAT }, {WOLF, GOAT}, FinalResult}
\*baitinv == TRUE
baitinv ==  TLCGet("level") < 10

(* --fair algorithm wolf_goat_cabbage {

variables side_start = FinalResult, side_end = {};

define {
    IsValidState(side) == ~(side \in InvalidStates)
    Inv == side_end # FinalResult
}

fair process (Farmer = 1) 
variable transport = {}; temp = {}; {
W:
    while (TRUE){
        either {
            \* pick an item from side_start and load it.
            await /\ transport = {} 
                  /\ side_start # {} /\ IsValidState(side_end);
            W1:
            \* choose an item such that this side is left valid:
            transport := {CHOOSE item \in side_start : IsValidState(side_start \ {item})};
            side_start := side_start \ transport;
        } or {
            \* pick an item from side_end and load it.
            await /\ transport = {} 
                  /\ side_end # {} /\ IsValidState(side_start);
            W2:
            \* choose an item such that this side is left valid:
            transport := {CHOOSE item \in side_end : IsValidState(side_end \ {item})};
            side_end := side_end \ transport;
        } or {
            \* leave an item to side_start side. If needed to avoid conflicts, load the other item.
            await transport # {};
            W3:
            side_start := side_start \union transport;
            transport := {};
        } or {
            \* leave an item to side_start side. If needed to avoid conflicts, load the other item.
            await transport # {};
            W4:
            side_end := side_end \union transport;
            transport := {};
        };
    }
}
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "e5742211")
VARIABLES side_start, side_end, pc

(* define statement *)
IsValidState(side) == ~(side \in InvalidStates)
Inv == side_end # FinalResult

VARIABLES transport, temp

vars == << side_start, side_end, pc, transport, temp >>

ProcSet == {1}

Init == (* Global variables *)
        /\ side_start = FinalResult
        /\ side_end = {}
        (* Process Farmer *)
        /\ transport = {}
        /\ temp = {}
        /\ pc = [self \in ProcSet |-> "W"]

W == /\ pc[1] = "W"
     /\ \/ /\ /\ transport = {}
              /\ side_start # {} /\ IsValidState(side_end)
           /\ pc' = [pc EXCEPT ![1] = "W1"]
        \/ /\ /\ transport = {}
              /\ side_end # {} /\ IsValidState(side_start)
           /\ pc' = [pc EXCEPT ![1] = "W2"]
        \/ /\ transport # {}
           /\ pc' = [pc EXCEPT ![1] = "W3"]
        \/ /\ transport # {}
           /\ pc' = [pc EXCEPT ![1] = "W4"]
     /\ UNCHANGED << side_start, side_end, transport, temp >>

W1 == /\ pc[1] = "W1"
      /\ transport' = {CHOOSE item \in side_start : IsValidState(side_start \ {item})}
      /\ side_start' = side_start \ transport'
      /\ pc' = [pc EXCEPT ![1] = "W"]
      /\ UNCHANGED << side_end, temp >>

W2 == /\ pc[1] = "W2"
      /\ transport' = {CHOOSE item \in side_end : IsValidState(side_end \ {item})}
      /\ side_end' = side_end \ transport'
      /\ pc' = [pc EXCEPT ![1] = "W"]
      /\ UNCHANGED << side_start, temp >>

W3 == /\ pc[1] = "W3"
      /\ side_start' = (side_start \union transport)
      /\ transport' = {}
      /\ pc' = [pc EXCEPT ![1] = "W"]
      /\ UNCHANGED << side_end, temp >>

W4 == /\ pc[1] = "W4"
      /\ side_end' = (side_end \union transport)
      /\ transport' = {}
      /\ pc' = [pc EXCEPT ![1] = "W"]
      /\ UNCHANGED << side_start, temp >>

Farmer == W \/ W1 \/ W2 \/ W3 \/ W4

Next == Farmer

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(Farmer)

\* END TRANSLATION 

TypeOk == /\ \A el \in side_start : el \in {WOLF, GOAT, CABBAGE} 
          /\ \A el \in side_end : el \in {WOLF, GOAT, CABBAGE}
          /\ \A el \in transport : el \in {WOLF, GOAT, CABBAGE}
    

====
