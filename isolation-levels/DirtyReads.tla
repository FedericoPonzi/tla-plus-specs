
---- MODULE DirtyReads ----
LOCAL INSTANCE TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE Integers
LOCAL INSTANCE Common

CONSTANTS Transactions

(*--algorithm dirty_reads {
    variables db_clock = -1;

 process (t \in Transactions)
 variables status = StatusInitial, item_time = -1; {
    S: while(status # StatusCompleted) {
    either {
            await status = StatusInitial;
            status := StatusReading;
            item_time := db_clock;
        } or {
            await status = StatusInitial;
            status := StatusWriting;
            item_time := db_clock; \* store to revert the state after the abort.
            db_clock := item_time + 1;
        } or {
            await status = StatusWriting;
            status := StatusAborted;
            db_clock := item_time;
        } or {
            await status \in {StatusReading, StatusWriting};
            status := StatusCompleted;
        }
    }
 }

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "64f38896" /\ chksum(tla) = "90a1c44a")
VARIABLES db_clock, pc, status, item_time

vars == << db_clock, pc, status, item_time >>

ProcSet == (Transactions)

Init == (* Global variables *)
        /\ db_clock = -1
        (* Process t *)
        /\ status = [self \in Transactions |-> StatusInitial]
        /\ item_time = [self \in Transactions |-> -1]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF status[self] # StatusCompleted
                 THEN /\ \/ /\ status[self] = StatusInitial
                            /\ status' = [status EXCEPT ![self] = StatusReading]
                            /\ item_time' = [item_time EXCEPT ![self] = db_clock]
                            /\ UNCHANGED db_clock
                         \/ /\ status[self] = StatusInitial
                            /\ status' = [status EXCEPT ![self] = StatusWriting]
                            /\ item_time' = [item_time EXCEPT ![self] = db_clock]
                            /\ db_clock' = item_time'[self] + 1
                         \/ /\ status[self] = StatusWriting
                            /\ status' = [status EXCEPT ![self] = StatusAborted]
                            /\ db_clock' = item_time[self]
                            /\ UNCHANGED item_time
                         \/ /\ status[self] \in {StatusReading, StatusWriting}
                            /\ status' = [status EXCEPT ![self] = StatusCompleted]
                            /\ UNCHANGED <<db_clock, item_time>>
                      /\ pc' = [pc EXCEPT ![self] = "S"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << db_clock, status, item_time >>

t(self) == S(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Transactions: t(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


DirtyReadAnomaly == \A tr \in Transactions: status[tr] = StatusCompleted => item_time[tr] <= db_clock
TypeOk == \A tr \in Transactions: 
                /\ status[tr] \in StatusType 
                /\ status[tr] = StatusInitial => item_time[tr] = -1
==========================
