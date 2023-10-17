

---- MODULE wolf_goat_cabbage ----
EXTENDS TLC, FiniteSets, Integers

WOLF == "Wolf"
GOAT == "Goat"
CABBAGE == "Cabbage"
FinalResult == {WOLF, GOAT, CABBAGE}
InvalidStates == {{CABBAGE,GOAT }, {WOLF, GOAT}}
baitinv == TRUE
\*baitinv ==  TLCGet("level") < 7

(* --fair algorithm wolf_goat_cabbage {

variables side_start = FinalResult, side_end = {};

define {
    IsValidState(side) == \/ FinalResult = side 
                          \/ ~(side \in InvalidStates)
    Inv == side_end # FinalResult
}
macro PickWithEmptyTransport(side) {
    await /\ transport = {} 
          /\ side # {};
    transport := {CHOOSE item \in side : /\ IsValidState(side \ {item})};
    side := side \ transport;
}
macro LeaveOrSwap(side) {
    await transport # {};
    temp := side;
    side := IF IsValidState(temp \union transport) THEN temp \union transport ELSE transport;
    transport := IF IsValidState(temp \union transport) THEN temp ELSE {};
}

fair process (Farmer = 1) 
variable transport = {}; temp = {}; {
W:
    while (TRUE){
        either {
            \* pick an item from side_start and load it.
            PickWithEmptyTransport(side_start);
        } or {
            \* pick an item from side_start and load it.
            PickWithEmptyTransport(side_end);
        } or {
            \* leave an item to side_start side. If needed to avoid conflicts, load the other item.
            LeaveOrSwap(side_start);
        } or {
            \* leave an item to side_end side. If needed to avoid conflicts, load the other item.
            LeaveOrSwap(side_end);
        };
    }
}
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "d6182a23")
VARIABLES side_start, side_end

(* define statement *)
IsValidState(side) == \/ FinalResult = side
                      \/ ~(side \in InvalidStates)
Inv == side_end # FinalResult

VARIABLES transport, temp

vars == << side_start, side_end, transport, temp >>

ProcSet == {1}

Init == (* Global variables *)
        /\ side_start = FinalResult
        /\ side_end = {}
        (* Process Farmer *)
        /\ transport = {}
        /\ temp = {}

Farmer == \/ /\ /\ transport = {}
                /\ side_start # {}
             /\ transport' = {CHOOSE item \in side_start : /\ IsValidState(side_start \ {item})}
             /\ side_start' = side_start \ transport'
             /\ UNCHANGED <<side_end, temp>>
          \/ /\ /\ transport = {}
                /\ side_end # {}
             /\ transport' = {CHOOSE item \in side_end : /\ IsValidState(side_end \ {item})}
             /\ side_end' = side_end \ transport'
             /\ UNCHANGED <<side_start, temp>>
          \/ /\ transport # {}
             /\ temp' = side_start
             /\ side_start' = (IF IsValidState(temp' \union transport) THEN temp' \union transport ELSE transport)
             /\ transport' = IF IsValidState(temp' \union transport) THEN temp' ELSE {}
             /\ UNCHANGED side_end
          \/ /\ transport # {}
             /\ temp' = side_end
             /\ side_end' = (IF IsValidState(temp' \union transport) THEN temp' \union transport ELSE transport)
             /\ transport' = IF IsValidState(temp' \union transport) THEN temp' ELSE {}
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
