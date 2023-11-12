In the missionaries and cannibals problem, three missionaries and three cannibals must cross a river using 
a boat which can carry at most two people, under the constraint that, for both banks, if there are missionaries 
present on the bank, they cannot be outnumbered by cannibals (if they were, the cannibals would eat the missionaries). 
The boat cannot cross the river by itself with no people on board. 

https://en.m.wikipedia.org/wiki/Missionaries_and_cannibals_problem

---- MODULE missionaries_and_cannibals_problem ----
EXTENDS TLC, Naturals, FiniteSets
CONSTANTS Missionaries, Cannibals

All == Missionaries \union Cannibals
side_end == "side_end"
side_start == "side_start"
SidesOpposite == [side_start |-> side_end, side_end |-> side_start]
simm == Permutations(Missionaries)

baitinv == TRUE
\*baitinv ==  TLCGet("level") < 20

(* --fair algorithm missionaries_and_cannibals_problem {
    variables sides = [side_start |-> All, side_end |-> {}],
    boat = {}, boat_side = side_start; 
    define {
        NumberOfCommonElements(s, d) ==  Cardinality(s \intersect  d)
        SafeStates == {i \in SUBSET (All) : NumberOfCommonElements(i, Missionaries) >= NumberOfCommonElements(i, Cannibals) } \union SUBSET (Cannibals)
        IsSafeState(x) == x \in SafeStates
        BoatMaxSpace == 2
        BoatNeverOverfilled == Cardinality(boat) <= BoatMaxSpace
        TypeOk == /\ \A x \in SafeStates: x \subseteq All
                  /\ boat \subseteq All
                  /\ sides[side_end] \union sides[side_start] \union boat = All
                  /\ Cardinality(sides[side_end]) + Cardinality(sides[side_start]) + Cardinality(boat) = Cardinality(All)
                  /\ boat_side \in DOMAIN sides

        Inv == /\ sides[side_end] # All 
               /\ IsSafeState(sides[side_start])
               /\ IsSafeState(sides[side_end])
               /\ BoatNeverOverfilled
        
        BoatHasSpace == Cardinality(boat) < 2
        BoatNonEmpty == Cardinality(boat) > 0
        
        \* To print:
        \*PrintVal(id, exp) == Print(<<id, exp>>, TRUE)
        \*ASSUME PrintVal("Safe states:", SafeStates)
    }

    fair process (p \in Missionaries \union Cannibals)
    variables my_side = side_start;
    {
M:
        while(TRUE) {
            either {
                \* jump on
                await ~ (self \in boat);
                await boat_side = my_side;
                await BoatHasSpace;
                await IsSafeState(sides[boat_side] \ {self});
                boat := boat \union {self};
                sides[my_side] := sides[my_side] \ {self};
            }
            or {
                \* drop off
                await self \in boat;
                await IsSafeState(sides[boat_side] \union {self});
                await boat_side # my_side;
                boat := boat \ {self};
                my_side := boat_side;
                sides[my_side] := sides[my_side] \union  {self};
            }
        }
    }
    fair process (Boat = 1){
B:
        while(TRUE) {         
            \* wait for it to fill up and travel to the other side
            await BoatNonEmpty;
            boat_side := SidesOpposite[boat_side];
        }
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "23d889ca")
VARIABLES sides, boat, boat_side

(* define statement *)
NumberOfCommonElements(s, d) ==  Cardinality(s \intersect  d)
SafeStates == {i \in SUBSET (All) : NumberOfCommonElements(i, Missionaries) >= NumberOfCommonElements(i, Cannibals) } \union SUBSET (Cannibals)
IsSafeState(x) == x \in SafeStates
BoatMaxSpace == 2
BoatNeverOverfilled == Cardinality(boat) <= BoatMaxSpace
TypeOk == /\ \A x \in SafeStates: x \subseteq All
          /\ boat \subseteq All
          /\ sides[side_end] \union sides[side_start] \union boat = All
          /\ Cardinality(sides[side_end]) + Cardinality(sides[side_start]) + Cardinality(boat) = Cardinality(All)
          /\ boat_side \in DOMAIN sides

Inv == /\ sides[side_end] # All
       /\ IsSafeState(sides[side_start])
       /\ IsSafeState(sides[side_end])
       /\ BoatNeverOverfilled

BoatHasSpace == Cardinality(boat) < 2
BoatNonEmpty == Cardinality(boat) > 0

VARIABLE my_side

vars == << sides, boat, boat_side, my_side >>

ProcSet == (Missionaries \union Cannibals) \cup {1}

Init == (* Global variables *)
        /\ sides = [side_start |-> All, side_end |-> {}]
        /\ boat = {}
        /\ boat_side = side_start
        (* Process p *)
        /\ my_side = [self \in Missionaries \union Cannibals |-> side_start]

p(self) == /\ \/ /\ ~ (self \in boat)
                 /\ boat_side = my_side[self]
                 /\ BoatHasSpace
                 /\ IsSafeState(sides[boat_side] \ {self})
                 /\ boat' = (boat \union {self})
                 /\ sides' = [sides EXCEPT ![my_side[self]] = sides[my_side[self]] \ {self}]
                 /\ UNCHANGED my_side
              \/ /\ self \in boat
                 /\ IsSafeState(sides[boat_side] \union {self})
                 /\ boat_side # my_side[self]
                 /\ boat' = boat \ {self}
                 /\ my_side' = [my_side EXCEPT ![self] = boat_side]
                 /\ sides' = [sides EXCEPT ![my_side'[self]] = sides[my_side'[self]] \union  {self}]
           /\ UNCHANGED boat_side

Boat == /\ BoatNonEmpty
        /\ boat_side' = SidesOpposite[boat_side]
        /\ UNCHANGED << sides, boat, my_side >>

Next == Boat
           \/ (\E self \in Missionaries \union Cannibals: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Missionaries \union Cannibals : WF_vars(p(self))
        /\ WF_vars(Boat)

\* END TRANSLATION 

====
