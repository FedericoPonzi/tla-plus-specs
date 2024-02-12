Helpful explaination about the model: http://muratbuffalo.blogspot.com/2018/12/2-phase-commit-and-beyond.html

------------------- MODULE 2pc ----------------
EXTENDS Integers, TLC

CONSTANTS ResourceManagers

StateInitial == "Initial"
StateAccept == "Accept"
StateCommitted == "Committed"
StateAborted == "Aborted"
RmPossibleStates == {StateInitial, StateAccept, StateCommitted, StateAborted}   
baitinv == TLCGet("level") < 9

(* --algorithm 2pc {
    variables resourceManagerState = [rm \in ResourceManagers |-> StateInitial], 
              tmState = StateInitial;
    define {
        TypeOk == \A rm \in ResourceManagers: resourceManagerState[rm] \in RmPossibleStates

        CanCommit == \A rm \in ResourceManagers : 
                        resourceManagerState[rm] = StateAccept
        CanAbort == \A rm \in ResourceManagers :
                        resourceManagerState[rm] = StateAborted  
        Inv == /\ \E rm1 \in ResourceManagers: resourceManagerState[rm1] \in {StateCommitted} => ~ \E rm2 \in ResourceManagers : resourceManagerState[rm2] \in {StateAborted}
               \*/\ baitinv
               
        Terminate == \A rm \in ResourceManagers: resourceManagerState[rm] \in {StateCommitted, StateAborted}
    }

fair process (TransactionManager = 0) {
TM: 
    while(~ tmState \in {StateCommitted, StateAborted} ){
        either{
            await CanCommit;
            tmState := StateCommitted;
        } or {
            await CanAbort;
            tmState := StateAborted;
        }
    }
}
fair process (rm \in ResourceManagers) {
RM: 
    while(resourceManagerState[self] \in {StateInitial, StateAccept}){
        either {
            await resourceManagerState[self] = StateInitial;
            resourceManagerState[self] := StateAccept; 
        } or {
            await resourceManagerState[self] = StateAccept /\ tmState = StateCommitted;
    CanCommitRmAction:
            resourceManagerState[self] := StateCommitted;
        } or {
            await \/ resourceManagerState[self] = StateInitial
                  \/ /\ resourceManagerState[self] = StateAccept /\ tmState = StateInitial;
    CanAbortRmAction:
            resourceManagerState[self] := StateAborted;
        }
    }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c33de399" /\ chksum(tla) = "3f28490e")
VARIABLES resourceManagerState, tmState, pc

(* define statement *)
TypeOk == \A rm \in ResourceManagers: resourceManagerState[rm] \in RmPossibleStates

CanCommit == \A rm \in ResourceManagers :
                resourceManagerState[rm] = StateAccept
CanAbort == \A rm \in ResourceManagers :
                resourceManagerState[rm] = StateAborted
Inv == /\ \E rm1 \in ResourceManagers: resourceManagerState[rm1] \in {StateCommitted} => ~ \E rm2 \in ResourceManagers : resourceManagerState[rm2] \in {StateAborted}


Terminate == \A rm \in ResourceManagers: resourceManagerState[rm] \in {StateCommitted, StateAborted}


vars == << resourceManagerState, tmState, pc >>

ProcSet == {0} \cup (ResourceManagers)

Init == (* Global variables *)
        /\ resourceManagerState = [rm \in ResourceManagers |-> StateInitial]
        /\ tmState = StateInitial
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "TM"
                                        [] self \in ResourceManagers -> "RM"]

TM == /\ pc[0] = "TM"
      /\ IF ~ tmState \in {StateCommitted, StateAborted}
            THEN /\ \/ /\ CanCommit
                       /\ tmState' = StateCommitted
                    \/ /\ CanAbort
                       /\ tmState' = StateAborted
                 /\ pc' = [pc EXCEPT ![0] = "TM"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ UNCHANGED tmState
      /\ UNCHANGED resourceManagerState

TransactionManager == TM

RM(self) == /\ pc[self] = "RM"
            /\ IF resourceManagerState[self] \in {StateInitial, StateAccept}
                  THEN /\ \/ /\ resourceManagerState[self] = StateInitial
                             /\ resourceManagerState' = [resourceManagerState EXCEPT ![self] = StateAccept]
                             /\ pc' = [pc EXCEPT ![self] = "RM"]
                          \/ /\ resourceManagerState[self] = StateAccept /\ tmState = StateCommitted
                             /\ pc' = [pc EXCEPT ![self] = "CanCommitRmAction"]
                             /\ UNCHANGED resourceManagerState
                          \/ /\ \/ resourceManagerState[self] = StateInitial
                                \/ /\ resourceManagerState[self] = StateAccept /\ tmState = StateInitial
                             /\ pc' = [pc EXCEPT ![self] = "CanAbortRmAction"]
                             /\ UNCHANGED resourceManagerState
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED resourceManagerState
            /\ UNCHANGED tmState

CanCommitRmAction(self) == /\ pc[self] = "CanCommitRmAction"
                           /\ resourceManagerState' = [resourceManagerState EXCEPT ![self] = StateCommitted]
                           /\ pc' = [pc EXCEPT ![self] = "RM"]
                           /\ UNCHANGED tmState

CanAbortRmAction(self) == /\ pc[self] = "CanAbortRmAction"
                          /\ resourceManagerState' = [resourceManagerState EXCEPT ![self] = StateAborted]
                          /\ pc' = [pc EXCEPT ![self] = "RM"]
                          /\ UNCHANGED tmState

rm(self) == RM(self) \/ CanCommitRmAction(self) \/ CanAbortRmAction(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TransactionManager
           \/ (\E self \in ResourceManagers: rm(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(TransactionManager)
        /\ \A self \in ResourceManagers : WF_vars(rm(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 






==============

