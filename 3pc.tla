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

(* --algorithm 3pc {
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
        Terminate ==  <>[] \A rm \in ResourceManagers: rmStates[rm] \in {StateCommitted} /\ tmState = StateCommitted
    }

fair process (TransactionManager = 0) {
TM: 
    while(~ tmState \in {StateCommitted}){
        either{
            await tmState = StateInitial; 
            with (value \in Values) {
                proposedValue := value;
                tmState := StateCanCommit;
            }
        } or {
            await \E rm \in ResourceManagers: rmStates[rm] \in {StateAborted};
            tmState := StateInitial;
        } or {
            await tmState = StateCanCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateAcceptedCanCommit;
            tmState := StatePrecommit;
        } or {
            await tmState = StatePrecommit /\ \A rm \in ResourceManagers : rmStates[rm] = StatePrecommitted;
            tmState := StateDoCommit;
        } or {
            await tmState = StateDoCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateCommitted;
            tmState := StateCommitted;
        }
    }
}
fair process (rm \in ResourceManagers) {
RM: 
    while(~rmStates[self] \in {StateCommitted}){
        either {
            await rmStates[self] = StateInitial /\ tmState = StateCanCommit;
            \*either {
                rmStates[self] := StateAcceptedCanCommit; 
            \*} or {
            \*    rmStates[self] := StateAborted;
            \*}
        } or {
            await rmStates[self] = StateAcceptedCanCommit /\ tmState = StatePrecommit;
            \*either {
                rmStates[self] := StatePrecommitted;
            \*} or {
            \*    rmStates[self] := StateAborted;
            \*}
        } or {
            await /\ rmStates[self] = StatePrecommitted
                  /\ tmState = StateDoCommit;
            rmStates[self] := StateCommitted;
        }
    }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "bb7e3bb2" /\ chksum(tla) = "bf99caed")
VARIABLES rmStates, tmState, proposedValue, pc

(* define statement *)
TypeOk == /\ \A rm \in ResourceManagers: rmStates[rm] \in RmPossibleStates
          /\ tmState \in TmPossibleStates
          /\ proposedValue \in Values \union {-1}

Inv ==  /\ \E rm1 \in ResourceManagers: rmStates[rm1] \in {StateCommitted} =>
                ~ \E rm2 \in ResourceManagers : rmStates[rm2] \in {StateAborted}

chosen == {v \in Values: \A rm \in ResourceManagers: rmStates[rm] = StateCommitted /\ proposedValue = v}
Terminate ==  <>[] \A rm \in ResourceManagers: rmStates[rm] \in {StateCommitted} /\ tmState = StateCommitted


vars == << rmStates, tmState, proposedValue, pc >>

ProcSet == {0} \cup (ResourceManagers)

Init == (* Global variables *)
        /\ rmStates = [rm \in ResourceManagers |-> StateInitial]
        /\ tmState = StateInitial
        /\ proposedValue = -1
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "TM"
                                        [] self \in ResourceManagers -> "RM"]

TM == /\ pc[0] = "TM"
      /\ IF ~ tmState \in {StateCommitted}
            THEN /\ \/ /\ tmState = StateInitial
                       /\ \E value \in Values:
                            /\ proposedValue' = value
                            /\ tmState' = StateCanCommit
                    \/ /\ \E rm \in ResourceManagers: rmStates[rm] \in {StateAborted}
                       /\ tmState' = StateInitial
                       /\ UNCHANGED proposedValue
                    \/ /\ tmState = StateCanCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateAcceptedCanCommit
                       /\ tmState' = StatePrecommit
                       /\ UNCHANGED proposedValue
                    \/ /\ tmState = StatePrecommit /\ \A rm \in ResourceManagers : rmStates[rm] = StatePrecommitted
                       /\ tmState' = StateDoCommit
                       /\ UNCHANGED proposedValue
                    \/ /\ tmState = StateDoCommit /\ \A rm \in ResourceManagers : rmStates[rm] = StateCommitted
                       /\ tmState' = StateCommitted
                       /\ UNCHANGED proposedValue
                 /\ pc' = [pc EXCEPT ![0] = "TM"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ UNCHANGED << tmState, proposedValue >>
      /\ UNCHANGED rmStates

TransactionManager == TM

RM(self) == /\ pc[self] = "RM"
            /\ IF ~rmStates[self] \in {StateCommitted}
                  THEN /\ \/ /\ rmStates[self] = StateInitial /\ tmState = StateCanCommit
                             /\ rmStates' = [rmStates EXCEPT ![self] = StateAcceptedCanCommit]
                          \/ /\ rmStates[self] = StateAcceptedCanCommit /\ tmState = StatePrecommit
                             /\ rmStates' = [rmStates EXCEPT ![self] = StatePrecommitted]
                          \/ /\ /\ rmStates[self] = StatePrecommitted
                                /\ tmState = StateDoCommit
                             /\ rmStates' = [rmStates EXCEPT ![self] = StateCommitted]
                       /\ pc' = [pc EXCEPT ![self] = "RM"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmStates
            /\ UNCHANGED << tmState, proposedValue >>

rm(self) == RM(self)

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



C == INSTANCE Consensus 
        WITH  Value <- Values,  chosen <- chosen 



==============

