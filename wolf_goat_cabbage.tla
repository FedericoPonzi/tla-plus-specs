

---- MODULE wolf_goat_cabbage ----
EXTENDS TLC, FiniteSets, Integers

WOLF == "Wolf"
GOAT == "Goat"
CABBAGE == "Cabbage"
FinalResult == {WOLF, GOAT, CABBAGE}
baitinv == TRUE
\*baitinv ==  TLCGet("level") < 7

(* --fair algorithm wolf_goat_cabbage {

variables side_start = FinalResult, side_end = {};

define {
    IsValidState(side) == \/ FinalResult = side 
                          \/ ~(side \in {{CABBAGE,GOAT }, {WOLF, GOAT}})
    Inv == side_end # FinalResult
    PickFrom(side) == {CHOOSE item \in side : /\ IsValidState(side \ {item})}
}

macro PickWithEmptyTransport(side) {
    await /\ transport = {} 
          /\ side # {};
    transport := PickFrom(side);
    side := side \ transport;
}

macro Leave(side) {
    side := side \union transport;
    transport := {};
}

fair process (Farmer = 1) variable transport = {}; temp = {}, source = "";{
W:
    while (TRUE){
        either {
        \* pick an item from side_start and load it.
            PickWithEmptyTransport(side_start);
            source := "start";
        } or {
           PickWithEmptyTransport(side_end);
            source := "end";
        } or {
            await transport # {} /\ source = "end";
            temp := IF Cardinality(side_start) = 1 THEN {CHOOSE x \in side_start: TRUE} ELSE transport;
            side_start := IF IsValidState(side_start \union transport) THEN side_start \union transport ELSE (side_start \union transport) \ temp;
            transport := IF ~ \A e \in temp: e \in side_start THEN temp ELSE {};
            source := IF transport = {} THEN "" ELSE "start";
        } or {
            \* leave the item on either coast.
            await transport # {} /\ source = "start";
            temp := IF Cardinality(side_end) = 1 THEN {CHOOSE x \in side_end: TRUE} ELSE transport;
            side_end := IF IsValidState(side_end \union transport) THEN side_end \union transport ELSE (side_end \union transport) \ temp;
            transport := IF ~ \A e \in temp: e \in side_end THEN temp ELSE {};
            source := IF transport = {} THEN "" ELSE "end";
        };
    }
}
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "d2f548b1")
VARIABLES side_start, side_end

(* define statement *)
IsValidState(side) == \/ FinalResult = side
                      \/ ~(side \in {{CABBAGE,GOAT }, {WOLF, GOAT}})
Inv == side_end # FinalResult
PickFrom(side) == {CHOOSE item \in side : /\ IsValidState(side \ {item})}

VARIABLES transport, temp, source

vars == << side_start, side_end, transport, temp, source >>

ProcSet == {1}

Init == (* Global variables *)
        /\ side_start = FinalResult
        /\ side_end = {}
        (* Process Farmer *)
        /\ transport = {}
        /\ temp = {}
        /\ source = ""

Farmer == \/ /\ /\ transport = {}
                /\ side_start # {}
             /\ transport' = PickFrom(side_start)
             /\ side_start' = side_start \ transport'
             /\ source' = "start"
             /\ UNCHANGED <<side_end, temp>>
          \/ /\ /\ transport = {}
                /\ side_end # {}
             /\ transport' = PickFrom(side_end)
             /\ side_end' = side_end \ transport'
             /\ source' = "end"
             /\ UNCHANGED <<side_start, temp>>
          \/ /\ transport # {} /\ source = "end"
             /\ temp' = (IF Cardinality(side_start) = 1 THEN {CHOOSE x \in side_start: TRUE} ELSE transport)
             /\ side_start' = (IF IsValidState(side_start \union transport) THEN side_start \union transport ELSE (side_start \union transport) \ temp')
             /\ transport' = (IF ~ \A e \in temp': e \in side_start' THEN temp' ELSE {})
             /\ source' = (IF transport' = {} THEN "" ELSE "start")
             /\ UNCHANGED side_end
          \/ /\ transport # {} /\ source = "start"
             /\ temp' = (IF Cardinality(side_end) = 1 THEN {CHOOSE x \in side_end: TRUE} ELSE transport)
             /\ side_end' = (IF IsValidState(side_end \union transport) THEN side_end \union transport ELSE (side_end \union transport) \ temp')
             /\ transport' = (IF ~ \A e \in temp': e \in side_end' THEN temp' ELSE {})
             /\ source' = (IF transport' = {} THEN "" ELSE "end")
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
