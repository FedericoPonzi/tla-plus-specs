----- MODULE PhantomReads ----
LOCAL INSTANCE TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE Integers
LOCAL INSTANCE Common

CONSTANTS Transactions

(*--algorithm non_repeatable_reads {
    variables db = <<>>;

 process (t \in Transactions)
 variables status = StatusInitial, total_size = 0; {
    S: while(status # StatusCompleted) {
    either {
            await status \in {StatusInitial, StatusReading};
            status := StatusReading;
            assert total_size <= Len(db);
            total_size = Len(db);
        } or {
            await status = StatusInitial;
            status := StatusWriting;
            db := Append(db, 1); \* what we insert doesn't matter
        } or {
            await status \in {StatusReading, StatusWriting};
            status := StatusCompleted;
        }
    }
 }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "451b5320" /\ chksum(tla) = "3b689ba6")
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
                 THEN /\ \/ /\ status[self] \in {StatusInitial, StatusReading}
                            /\ status' = [status EXCEPT ![self] = StatusReading]
                            /\ item_time' = [item_time EXCEPT ![self] = db_clock]
                            /\ UNCHANGED db_clock
                         \/ /\ status[self] = StatusInitial
                            /\ status' = [status EXCEPT ![self] = StatusWriting]
                            /\ item_time' = [item_time EXCEPT ![self] = db_clock]
                            /\ db_clock' = item_time'[self] + 1
                         \/ /\ status[self] = StatusReading
                            /\ Assert(item_time[self] = db_clock, 
                                      "Failure of assertion at line 27, column 13.")
                            /\ UNCHANGED <<db_clock, status, item_time>>
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

TypeOk == \A tr \in Transactions: 
                /\ status[tr] \in StatusType 
                /\ status[tr] = StatusInitial => item_time[tr] = -1
====
