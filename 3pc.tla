The Three-Phase Commit Protocol (3PC) is a distributed transaction protocol used to ensure the consistency of 
distributed databases or systems where multiple participants need to agree on whether a transaction should be 
committed or aborted. It is an improvement over the Two-Phase Commit (2PC) protocol, aiming to eliminate some 
f the issues related to blocking and uncertainty that can occur in 2PC. The 3PC protocol divides the commit 
process into three phases: the "CanCommit" phase, the "PreCommit" phase, and the "DoCommit" phase.

3pc achieves liveness as it can commit in the event of failures as it can just timeout and retry, but it fails on 
correctness for async networks with a single network delayed TC or RM (network partition).

Running this spec with NetworkPartitions = TRUE leads to a stack trace in which one RM goes to Committed and the other 
one along with TM go to AbortedTransaction.

Resources:
* https://www.cs.columbia.edu/~du/ds/assets/lectures/lecture17.pdf
* http://muratbuffalo.blogspot.com/2018/12/2-phase-commit-and-beyond.html


------------------- MODULE 3pc ----------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS ResourceManagers, Values, NetworkPartitions


StateInitial == "Initial"

StateCanCommit == "CanCommit"
StateAcceptedCanCommit == "AcceptedCanCommit"

StateAborted == "AbortedTransaction"

StatePrecommit == "PreCommit"
StatePrecommitted == "PreCommitted"

StateDoCommit == "DoCommit"
StateCommitted == "Committed"

StatePartitioned == "NetworkPartitions"

TmPossibleStates == {StateInitial, StateCanCommit, StateAborted, StatePrecommit, StateDoCommit, StateCommitted, StatePartitioned}
RmPossibleStates == {StateInitial, StateAcceptedCanCommit, StateAborted, StatePrecommitted, StateCommitted, StatePartitioned}
EndStates == {StateCommitted, StateAborted}

baitinv == TLCGet("level") < 29


(* --fair algorithm 3pc {
    variables rmStates = [rm \in ResourceManagers |-> StateInitial], 
              tmState = StateInitial,
              proposedValue = -1;
    define {
        TypeOk == /\ \A rm \in ResourceManagers: rmStates[rm] \in RmPossibleStates
                  /\ tmState \in TmPossibleStates
                  /\ proposedValue \in Values \union {-1}
        
        Inv ==  \A rm1 \in ResourceManagers: rmStates[rm1] = StateAborted =>
                    ~\E rm2 \in ResourceManagers: rmStates[rm2] = StateCommitted
        chosen == {v \in Values: \A rm \in ResourceManagers: rmStates[rm] = StateCommitted /\ proposedValue = v}
        Terminate ==  <>[] /\ \A rm \in ResourceManagers: rmStates[rm] \in EndStates
                           /\ tmState \in EndStates
    }

fair process (TransactionManager = 0) 
variable pre = ""; {
TM: 
    while(tmState \notin {StateCommitted, StateAborted}){
        either{
            await tmState = StateInitial; 
            with (value \in Values) {
                proposedValue := value;
                tmState := StateCanCommit;
            }
        } or {
            await \E rm \in ResourceManagers: 
                    rmStates[rm] = StateAborted;
TM_AB:            tmState := StateAborted;
        } or {
            await tmState = StateCanCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateAcceptedCanCommit;
TM_PRE:            tmState := StatePrecommit;
        } or {
            await tmState = StatePrecommit /\ \A rm \in ResourceManagers : rmStates[rm] \in {StatePrecommitted, StateCommitted};
TM_DOC:            tmState := StateDoCommit;
        } or {
            await tmState = StateDoCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateCommitted;
TM_COM:            tmState := StateCommitted;
        } or { 
           await NetworkPartitions /\ pre # tmState;
           pre := tmState;
           tmState := StatePartitioned;
TM_PAR:        tmState := pre;
        } or {
            \* timeout causes abort
            await \E rm \in ResourceManagers : rmStates[rm] = StatePartitioned;
            tmState:= StateAborted;
        }
    }
}
fair process (rm \in ResourceManagers)   variables pre=""; {

RM: 
    while(rmStates[self] \notin {StateCommitted, StateAborted}) {
        either {
            await rmStates[self] = StateInitial /\ tmState = StateCanCommit;
RM_CAN:            either {
                rmStates[self] := StateAcceptedCanCommit; 
            } or {
                rmStates[self] := StateAborted;
            }
        } or {
            await rmStates[self] = StateAcceptedCanCommit /\ tmState = StatePrecommit;
RM_PRE:            either {
                rmStates[self] := StatePrecommitted;
            } or {
                rmStates[self] := StateAborted;
            }
        } or {
            await /\ rmStates[self] = StatePrecommitted
                  /\ tmState \in {StateDoCommit, StatePartitioned};
RM_COM:     
            rmStates[self] := StateCommitted;
            
        } or {
            await tmState = StateAborted;
RM_INI:            rmStates[self] := StateAborted;
        } or { 
           await NetworkPartitions /\ pre#rmStates[self];
           pre := rmStates[self];
           rmStates[self] := StatePartitioned;
RR:        rmStates[self] := pre;
        } or {
            await tmState = StatePartitioned /\ rmStates[self] = StateCanCommit;
            rmStates[self] := StateAborted;
        } or {
            await tmState = StatePartitioned /\ rmStates[self] = StatePrecommit;
            rmStates[self] := StateCommitted;
        }
    }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "175cddaa")
\* Process variable pre of process TransactionManager at line 55 col 10 changed to pre_
VARIABLES rmStates, tmState, proposedValue, pc

(* define statement *)
TypeOk == /\ \A rm \in ResourceManagers: rmStates[rm] \in RmPossibleStates
          /\ tmState \in TmPossibleStates
          /\ proposedValue \in Values \union {-1}

Inv ==  \A rm1 \in ResourceManagers: rmStates[rm1] = StateAborted =>
            ~\E rm2 \in ResourceManagers: rmStates[rm2] = StateCommitted
chosen == {v \in Values: \A rm \in ResourceManagers: rmStates[rm] = StateCommitted /\ proposedValue = v}
Terminate ==  <>[] /\ \A rm \in ResourceManagers: rmStates[rm] \in EndStates
                   /\ tmState \in EndStates

VARIABLES pre_, pre

vars == << rmStates, tmState, proposedValue, pc, pre_, pre >>

ProcSet == {0} \cup (ResourceManagers)

Init == (* Global variables *)
        /\ rmStates = [rm \in ResourceManagers |-> StateInitial]
        /\ tmState = StateInitial
        /\ proposedValue = -1
        (* Process TransactionManager *)
        /\ pre_ = ""
        (* Process rm *)
        /\ pre = [self \in ResourceManagers |-> ""]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "TM"
                                        [] self \in ResourceManagers -> "RM"]

TM == /\ pc[0] = "TM"
      /\ IF tmState \notin {StateCommitted, StateAborted}
            THEN /\ \/ /\ tmState = StateInitial
                       /\ \E value \in Values:
                            /\ proposedValue' = value
                            /\ tmState' = StateCanCommit
                       /\ pc' = [pc EXCEPT ![0] = "TM"]
                       /\ pre_' = pre_
                    \/ /\ \E rm \in ResourceManagers:
                            rmStates[rm] = StateAborted
                       /\ pc' = [pc EXCEPT ![0] = "TM_AB"]
                       /\ UNCHANGED <<tmState, proposedValue, pre_>>
                    \/ /\ tmState = StateCanCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateAcceptedCanCommit
                       /\ pc' = [pc EXCEPT ![0] = "TM_PRE"]
                       /\ UNCHANGED <<tmState, proposedValue, pre_>>
                    \/ /\ tmState = StatePrecommit /\ \A rm \in ResourceManagers : rmStates[rm] \in {StatePrecommitted, StateCommitted}
                       /\ pc' = [pc EXCEPT ![0] = "TM_DOC"]
                       /\ UNCHANGED <<tmState, proposedValue, pre_>>
                    \/ /\ tmState = StateDoCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateCommitted
                       /\ pc' = [pc EXCEPT ![0] = "TM_COM"]
                       /\ UNCHANGED <<tmState, proposedValue, pre_>>
                    \/ /\ NetworkPartitions /\ pre_ # tmState
                       /\ pre_' = tmState
                       /\ tmState' = StatePartitioned
                       /\ pc' = [pc EXCEPT ![0] = "TM_PAR"]
                       /\ UNCHANGED proposedValue
                    \/ /\ \E rm \in ResourceManagers : rmStates[rm] = StatePartitioned
                       /\ tmState' = StateAborted
                       /\ pc' = [pc EXCEPT ![0] = "TM"]
                       /\ UNCHANGED <<proposedValue, pre_>>
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ UNCHANGED << tmState, proposedValue, pre_ >>
      /\ UNCHANGED << rmStates, pre >>

TM_AB == /\ pc[0] = "TM_AB"
         /\ tmState' = StateAborted
         /\ pc' = [pc EXCEPT ![0] = "TM"]
         /\ UNCHANGED << rmStates, proposedValue, pre_, pre >>

TM_PRE == /\ pc[0] = "TM_PRE"
          /\ tmState' = StatePrecommit
          /\ pc' = [pc EXCEPT ![0] = "TM"]
          /\ UNCHANGED << rmStates, proposedValue, pre_, pre >>

TM_DOC == /\ pc[0] = "TM_DOC"
          /\ tmState' = StateDoCommit
          /\ pc' = [pc EXCEPT ![0] = "TM"]
          /\ UNCHANGED << rmStates, proposedValue, pre_, pre >>

TM_COM == /\ pc[0] = "TM_COM"
          /\ tmState' = StateCommitted
          /\ pc' = [pc EXCEPT ![0] = "TM"]
          /\ UNCHANGED << rmStates, proposedValue, pre_, pre >>

TM_PAR == /\ pc[0] = "TM_PAR"
          /\ tmState' = pre_
          /\ pc' = [pc EXCEPT ![0] = "TM"]
          /\ UNCHANGED << rmStates, proposedValue, pre_, pre >>

TransactionManager == TM \/ TM_AB \/ TM_PRE \/ TM_DOC \/ TM_COM \/ TM_PAR

RM(self) == /\ pc[self] = "RM"
            /\ IF rmStates[self] \notin {StateCommitted, StateAborted}
                  THEN /\ \/ /\ rmStates[self] = StateInitial /\ tmState = StateCanCommit
                             /\ pc' = [pc EXCEPT ![self] = "RM_CAN"]
                             /\ UNCHANGED <<rmStates, pre>>
                          \/ /\ rmStates[self] = StateAcceptedCanCommit /\ tmState = StatePrecommit
                             /\ pc' = [pc EXCEPT ![self] = "RM_PRE"]
                             /\ UNCHANGED <<rmStates, pre>>
                          \/ /\ /\ rmStates[self] = StatePrecommitted
                                /\ tmState \in {StateDoCommit, StatePartitioned}
                             /\ pc' = [pc EXCEPT ![self] = "RM_COM"]
                             /\ UNCHANGED <<rmStates, pre>>
                          \/ /\ tmState = StateAborted
                             /\ pc' = [pc EXCEPT ![self] = "RM_INI"]
                             /\ UNCHANGED <<rmStates, pre>>
                          \/ /\ NetworkPartitions /\ pre[self]#rmStates[self]
                             /\ pre' = [pre EXCEPT ![self] = rmStates[self]]
                             /\ rmStates' = [rmStates EXCEPT ![self] = StatePartitioned]
                             /\ pc' = [pc EXCEPT ![self] = "RR"]
                          \/ /\ tmState = StatePartitioned /\ rmStates[self] = StateCanCommit
                             /\ rmStates' = [rmStates EXCEPT ![self] = StateAborted]
                             /\ pc' = [pc EXCEPT ![self] = "RM"]
                             /\ pre' = pre
                          \/ /\ tmState = StatePartitioned /\ rmStates[self] = StatePrecommit
                             /\ rmStates' = [rmStates EXCEPT ![self] = StateCommitted]
                             /\ pc' = [pc EXCEPT ![self] = "RM"]
                             /\ pre' = pre
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << rmStates, pre >>
            /\ UNCHANGED << tmState, proposedValue, pre_ >>

RM_CAN(self) == /\ pc[self] = "RM_CAN"
                /\ \/ /\ rmStates' = [rmStates EXCEPT ![self] = StateAcceptedCanCommit]
                   \/ /\ rmStates' = [rmStates EXCEPT ![self] = StateAborted]
                /\ pc' = [pc EXCEPT ![self] = "RM"]
                /\ UNCHANGED << tmState, proposedValue, pre_, pre >>

RM_PRE(self) == /\ pc[self] = "RM_PRE"
                /\ \/ /\ rmStates' = [rmStates EXCEPT ![self] = StatePrecommitted]
                   \/ /\ rmStates' = [rmStates EXCEPT ![self] = StateAborted]
                /\ pc' = [pc EXCEPT ![self] = "RM"]
                /\ UNCHANGED << tmState, proposedValue, pre_, pre >>

RM_COM(self) == /\ pc[self] = "RM_COM"
                /\ rmStates' = [rmStates EXCEPT ![self] = StateCommitted]
                /\ pc' = [pc EXCEPT ![self] = "RM"]
                /\ UNCHANGED << tmState, proposedValue, pre_, pre >>

RM_INI(self) == /\ pc[self] = "RM_INI"
                /\ rmStates' = [rmStates EXCEPT ![self] = StateAborted]
                /\ pc' = [pc EXCEPT ![self] = "RM"]
                /\ UNCHANGED << tmState, proposedValue, pre_, pre >>

RR(self) == /\ pc[self] = "RR"
            /\ rmStates' = [rmStates EXCEPT ![self] = pre[self]]
            /\ pc' = [pc EXCEPT ![self] = "RM"]
            /\ UNCHANGED << tmState, proposedValue, pre_, pre >>

rm(self) == RM(self) \/ RM_CAN(self) \/ RM_PRE(self) \/ RM_COM(self)
               \/ RM_INI(self) \/ RR(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TransactionManager
           \/ (\E self \in ResourceManagers: rm(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(TransactionManager)
        /\ \A self \in ResourceManagers : WF_vars(rm(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 



C == INSTANCE Consensus 
        WITH  Value <- Values,  chosen <- chosen 



==============

