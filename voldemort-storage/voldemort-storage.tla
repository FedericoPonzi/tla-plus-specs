This is my solution to Murat Demibras first tla+ project. I decided to not reuse the provided 
template.

From: https://muratbuffalo.blogspot.com/2016/11/modeling-replicated-storage-system-in.html?m=1
 
> I assigned the students to model Voldemort with client-side routing as their first project.

> Here is the protocol. The client reads the highest version number "hver" from the read quorum (ReadQ). 
The client then writes to the write quorum nodes (WriteQ) the store the updated record with "hver+1" 
version number. The storage nodes can crash or recover, provided that no more than FAILNUM number of 
nodes are crashed at any moment. Our WriteQ and ReadQ selection will consist of the lowest id storage 
nodes that are up (currently not failed).

> I asked the students to model check with different combinations of ReadQ, WriteQ, and FAILNUM, and 
figure out the relation that needs to be satisfied among these configuration parameters in order to 
ensure that the protocol satisfies the single-copy consistency property. I wanted my students to see 
how consistency can be violated as a result of a series of unfortunate events (such as untimely node 
death and recoveries). The model checker is very good for producing counterexamples where consistency 
is violated.
> We simplified things by modeling the storing (and updating) of just a single data item, so we didn't have to model the hashing part. We also used shared memory. The client directly writes (say via an RPC) to the db of the storage nodes. 
> I also gave the students the template for the model. 

I've committed the base template separately in this repo (check history) in case you want to give it a stab yourself.


----------------- MODULE voldemort_storage ------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, C, STOP, ReadQ, WriteQ, FAILNUM

ASSUME /\ N = 5 /\ C = 1 /\ STOP < 10 
       /\ 0 < ReadQ /\ ReadQ < 4
       /\ 0 < WriteQ /\ WriteQ < 4
       /\ 0 <= FAILNUM /\ FAILNUM < 3

Nodes == 1..N
Clients == N + 1..N + C \* should give dfifenr ID space to Client.

(* --algorithm voldemort {
    variables FailNum = FAILNUM,
             up = [n \in Nodes |-> TRUE], \* Initially all nodes are up
             db = [n \in Nodes |-> {[ver -> 0, val -> 0]}];
             \* All nodes have database, wherein [ver = 0, val = 0] stored for the item.
    define {
        UpNodes == {}
        ReturnReadQ == 
        ReturnWriteQ == CHOOSE  i \in SUBSET (UpNodes) : Cardinality(i) = WriteQ
        \* CHOOSE deterministically returns lowest ID nodes that satisfy the requirement.
    }
    fair process ( c \in Clients)
    variable cntr = 0, hver = 0, Q = {};
    {
        CL: while (cntr <= STOP ) {
            cntr := cntr + 1;
            \* get the highest version number from read Quorum

            \* write val = cntr to writeQuorum with higher version number




        }
    }
    fair process (n \in Nodes) 
    {
        NODE: while( TRUE ) {
            if ( FailNum > 0 /\ up[self] = TRUE) { \* Storage node can fail
                \* Remove me: added to make pluscal compile.
                FailNum := failNum + 1 ;

            } else if ( up[self] = FALSE ){ \* or recover
                \* Remove me: added to make pluscal compile.
                FailNum := failNum + 1 ;
            } 
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "84217caf" /\ chksum(tla) = "31d33f57")
VARIABLES FailNum, up, db, pc

(* define statement *)
UpNodes == {}
ReturnReadQ ==
ReturnWriteQ == CHOOSE  i \in SUBSET (UpNodes) : Cardinality(i) = WriteQ

VARIABLES cntr, hver, Q

vars == << FailNum, up, db, pc, cntr, hver, Q >>

ProcSet == (Clients) \cup (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ db = [n \in Nodes |-> {[ver -> 0, val -> 0]}]
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ hver = [self \in Clients |-> 0]
        /\ Q = [self \in Clients |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "CL"
                                        [] self \in Nodes -> "NODE"]

CL(self) == /\ pc[self] = "CL"
            /\ IF cntr[self] <= STOP
                  THEN /\ cntr' = [cntr EXCEPT ![self] = cntr[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "CL"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ cntr' = cntr
            /\ UNCHANGED << FailNum, up, db, hver, Q >>

c(self) == CL(self)

NODE(self) == /\ pc[self] = "NODE"
              /\ IF FailNum > 0 /\ up[self] = TRUE
                    THEN /\ FailNum' = failNum + 1
                    ELSE /\ IF up[self] = FALSE
                               THEN /\ FailNum' = failNum + 1
                               ELSE /\ TRUE
                                    /\ UNCHANGED FailNum
              /\ pc' = [pc EXCEPT ![self] = "NODE"]
              /\ UNCHANGED << up, db, cntr, hver, Q >>

n(self) == NODE(self)

Next == (\E self \in Clients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(c(self))
        /\ \A self \in Nodes : WF_vars(n(self))

\* END TRANSLATION 


====
