The Three-Phase Commit Protocol (3PC) is a distributed transaction protocol used to ensure the consistency of distributed databases or systems where multiple participants need to agree on whether a transaction should be committed or aborted. It is an improvement over the Two-Phase Commit (2PC) protocol, aiming to eliminate some of the issues related to blocking and uncertainty that can occur in 2PC. The 3PC protocol divides the commit process into three phases: the "CanCommit" phase, the "PreCommit" phase, and the "DoCommit" phase.

Here is a description of each phase in the Three-Phase Commit Protocol:

CanCommit Phase:
    In this phase, the coordinator (the entity responsible for managing the distributed transaction) sends a "CanCommit" request to all participating nodes or participants.
    Each participant examines its local state and determines whether it is willing to commit the transaction. If the participant's local conditions are met (e.g., it has the necessary resources and constraints are satisfied), it replies with a "Yes" message. If not, it replies with a "No" message.
    The coordinator waits for responses from all participants.

PreCommit Phase:
    If all participants respond with a "Yes" in the CanCommit phase, the coordinator moves to the PreCommit phase. Otherwise, if any participant responds with a "No," the coordinator aborts the transaction immediately.
    In the PreCommit phase, the coordinator sends a "PreCommit" message to all participants to signal that they can proceed with the transaction.
    Participants, upon receiving the PreCommit message, record the decision but do not commit the transaction yet.
    At this point, participants have tentatively agreed to commit the transaction but have not yet made it permanent.

DoCommit Phase:
    After entering the PreCommit phase, the coordinator waits for acknowledgments from all participants to confirm that they have successfully recorded the decision.
    If all acknowledgments are received, the coordinator sends a "DoCommit" message to all participants, instructing them to make the transaction permanent.
    Participants, upon receiving the DoCommit message, perform the final commit operation. If any participant encounters an issue during this phase, it can still abort the transaction and inform the coordinator.
    Once all participants have confirmed the successful completion of the commit operation, the coordinator considers the transaction committed and notifies all participants accordingly.

The Three-Phase Commit Protocol aims to strike a balance between the blocking nature of the Two-Phase Commit Protocol (where participants can be stuck indefinitely waiting for a decision) and the lack of fault tolerance in the One-Phase Commit Protocol. However, it is worth noting that 3PC does not completely eliminate all possible issues in distributed transactions, and it may still suffer from some of the same problems as 2PC in certain scenarios, such as network failures or coordinator failures.

3pc achieves liveness as it can commit in the event of failures as it can just timeout and retry, but it fails on correctness for async networks with a single network delayed TC or RM (network partition).




------------------- MODULE 3pc ----------------
EXTENDS Integers, TLC

CONSTANTS ResourceManagers, Values


StateInitial == "Initial"

StateCanCommit == "CanCommit"
StateAcceptedCanCommit == "AcceptedCanCommit"

StateAborted == "AbortedTransaction"

StatePrecommit == "PreCommit"
StatePrecommitted == "PreCommitted"

StateDoCommit == "DoCommit"
StateCommitted == "Committed"

TmPossibleStates == {StateInitial, StateCanCommit, StateAborted, StatePrecommit, StateDoCommit, StateCommitted}
RmPossibleStates == {StateInitial, StateAcceptedCanCommit, StateAborted, StatePrecommitted, StateCommitted}

baitinv == TLCGet("level") < 9

(* --fair algorithm 3pc {
    variables rmStates = [rm \in ResourceManagers |-> StateInitial], 
              tmState = StateInitial,
              proposedValue = -1;
    define {
        TypeOk == /\ \A rm \in ResourceManagers: rmStates[rm] \in RmPossibleStates
                  /\ tmState \in TmPossibleStates
                  /\ proposedValue \in Values \union {-1}
        
        Inv ==  /\ \E rm1 \in ResourceManagers: rmStates[rm1] \in {StateCommitted} => 
                        ~ \E rm2 \in ResourceManagers : rmStates[rm2] \in {StateAborted}
                \*/\ baitinv
        chosen == {v \in Values: \A rm \in ResourceManagers: rmStates[rm] = StateCommitted /\ proposedValue = v}
        Terminate ==  <>[] \A rm \in ResourceManagers: rmStates[rm] = tmState
    }

fair process (TransactionManager = 0) {
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
            await tmState = StatePrecommit /\ \A rm \in ResourceManagers : rmStates[rm] = StatePrecommitted;
TM_DOC:            tmState := StateDoCommit;
        } or {
            await tmState = StateDoCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateCommitted;
TM_COM:            tmState := StateCommitted;
        }
    }
}
fair process (rm \in ResourceManagers) {
RM: 
    while(rmStates[self] \notin {StateCommitted, StateAborted}){
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
                  /\ tmState = StateDoCommit;
RM_COM:           rmStates[self] := StateCommitted;
        } or {
            await tmState = StateAborted;
RM_INI:            rmStates[self] := StateAborted;
        } 
    }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "b56d638")
VARIABLES rmStates, tmState, proposedValue, pc

(* define statement *)
TypeOk == /\ \A rm \in ResourceManagers: rmStates[rm] \in RmPossibleStates
          /\ tmState \in TmPossibleStates
          /\ proposedValue \in Values \union {-1}

Inv ==  /\ \E rm1 \in ResourceManagers: rmStates[rm1] \in {StateCommitted} =>
                ~ \E rm2 \in ResourceManagers : rmStates[rm2] \in {StateAborted}

chosen == {v \in Values: \A rm \in ResourceManagers: rmStates[rm] = StateCommitted /\ proposedValue = v}
Terminate ==  <>[] \A rm \in ResourceManagers: rmStates[rm] = tmState


vars == << rmStates, tmState, proposedValue, pc >>

ProcSet == {0} \cup (ResourceManagers)

Init == (* Global variables *)
        /\ rmStates = [rm \in ResourceManagers |-> StateInitial]
        /\ tmState = StateInitial
        /\ proposedValue = -1
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "TM"
                                        [] self \in ResourceManagers -> "RM"]

TM == /\ pc[0] = "TM"
      /\ IF tmState \notin {StateCommitted, StateAborted}
            THEN /\ \/ /\ tmState = StateInitial
                       /\ \E value \in Values:
                            /\ proposedValue' = value
                            /\ tmState' = StateCanCommit
                       /\ pc' = [pc EXCEPT ![0] = "TM"]
                    \/ /\ \E rm \in ResourceManagers:
                            rmStates[rm] = StateAborted
                       /\ pc' = [pc EXCEPT ![0] = "TM_AB"]
                       /\ UNCHANGED <<tmState, proposedValue>>
                    \/ /\ tmState = StateCanCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateAcceptedCanCommit
                       /\ pc' = [pc EXCEPT ![0] = "TM_PRE"]
                       /\ UNCHANGED <<tmState, proposedValue>>
                    \/ /\ tmState = StatePrecommit /\ \A rm \in ResourceManagers : rmStates[rm] = StatePrecommitted
                       /\ pc' = [pc EXCEPT ![0] = "TM_DOC"]
                       /\ UNCHANGED <<tmState, proposedValue>>
                    \/ /\ tmState = StateDoCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateCommitted
                       /\ pc' = [pc EXCEPT ![0] = "TM_COM"]
                       /\ UNCHANGED <<tmState, proposedValue>>
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ UNCHANGED << tmState, proposedValue >>
      /\ UNCHANGED rmStates

TM_AB == /\ pc[0] = "TM_AB"
         /\ tmState' = StateAborted
         /\ pc' = [pc EXCEPT ![0] = "TM"]
         /\ UNCHANGED << rmStates, proposedValue >>

TM_PRE == /\ pc[0] = "TM_PRE"
          /\ tmState' = StatePrecommit
          /\ pc' = [pc EXCEPT ![0] = "TM"]
          /\ UNCHANGED << rmStates, proposedValue >>

TM_DOC == /\ pc[0] = "TM_DOC"
          /\ tmState' = StateDoCommit
          /\ pc' = [pc EXCEPT ![0] = "TM"]
          /\ UNCHANGED << rmStates, proposedValue >>

TM_COM == /\ pc[0] = "TM_COM"
          /\ tmState' = StateCommitted
          /\ pc' = [pc EXCEPT ![0] = "TM"]
          /\ UNCHANGED << rmStates, proposedValue >>

TransactionManager == TM \/ TM_AB \/ TM_PRE \/ TM_DOC \/ TM_COM

RM(self) == /\ pc[self] = "RM"
            /\ IF rmStates[self] \notin {StateCommitted, StateAborted}
                  THEN /\ \/ /\ rmStates[self] = StateInitial /\ tmState = StateCanCommit
                             /\ pc' = [pc EXCEPT ![self] = "RM_CAN"]
                          \/ /\ rmStates[self] = StateAcceptedCanCommit /\ tmState = StatePrecommit
                             /\ pc' = [pc EXCEPT ![self] = "RM_PRE"]
                          \/ /\ /\ rmStates[self] = StatePrecommitted
                                /\ tmState = StateDoCommit
                             /\ pc' = [pc EXCEPT ![self] = "RM_COM"]
                          \/ /\ tmState = StateAborted
                             /\ pc' = [pc EXCEPT ![self] = "RM_INI"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << rmStates, tmState, proposedValue >>

RM_CAN(self) == /\ pc[self] = "RM_CAN"
                /\ \/ /\ rmStates' = [rmStates EXCEPT ![self] = StateAcceptedCanCommit]
                   \/ /\ rmStates' = [rmStates EXCEPT ![self] = StateAborted]
                /\ pc' = [pc EXCEPT ![self] = "RM"]
                /\ UNCHANGED << tmState, proposedValue >>

RM_PRE(self) == /\ pc[self] = "RM_PRE"
                /\ \/ /\ rmStates' = [rmStates EXCEPT ![self] = StatePrecommitted]
                   \/ /\ rmStates' = [rmStates EXCEPT ![self] = StateAborted]
                /\ pc' = [pc EXCEPT ![self] = "RM"]
                /\ UNCHANGED << tmState, proposedValue >>

RM_COM(self) == /\ pc[self] = "RM_COM"
                /\ rmStates' = [rmStates EXCEPT ![self] = StateCommitted]
                /\ pc' = [pc EXCEPT ![self] = "RM"]
                /\ UNCHANGED << tmState, proposedValue >>

RM_INI(self) == /\ pc[self] = "RM_INI"
                /\ rmStates' = [rmStates EXCEPT ![self] = StateAborted]
                /\ pc' = [pc EXCEPT ![self] = "RM"]
                /\ UNCHANGED << tmState, proposedValue >>

rm(self) == RM(self) \/ RM_CAN(self) \/ RM_PRE(self) \/ RM_COM(self)
               \/ RM_INI(self)

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

