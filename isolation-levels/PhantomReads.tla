----- MODULE PhantomReads ----
LOCAL INSTANCE TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE Integers
LOCAL INSTANCE Common
LOCAL INSTANCE Sequences

CONSTANTS Transactions
baitinv == TRUE \* TLCGet("level") < 7

(*--fair algorithm non_repeatable_reads {
    variables db = <<>>;

 fair process (t \in Transactions)
 variables status = StatusInitial, total_size = 0; {
    S: while(status # StatusCompleted) {
    either {
            await status \in {StatusInitial, StatusReading};
            status := StatusReading;
            assert Len(db) <= total_size;
            total_size := Len(db);
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
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "b3f21775")
VARIABLES db, pc, status, total_size

vars == << db, pc, status, total_size >>

ProcSet == (Transactions)

Init == (* Global variables *)
        /\ db = <<>>
        (* Process t *)
        /\ status = [self \in Transactions |-> StatusInitial]
        /\ total_size = [self \in Transactions |-> 0]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF status[self] # StatusCompleted
                 THEN /\ \/ /\ status[self] \in {StatusInitial, StatusReading}
                            /\ status' = [status EXCEPT ![self] = StatusReading]
                            /\ PrintT("Len db:")
                            /\ PrintT(Len(db))
                            /\ PrintT(total_size[self])
                            /\ Assert(Len(db) <= total_size[self], 
                                      "Failure of assertion at line 23, column 13.")
                            /\ total_size' = [total_size EXCEPT ![self] = Len(db)]
                            /\ db' = db
                         \/ /\ status[self] = StatusInitial
                            /\ status' = [status EXCEPT ![self] = StatusWriting]
                            /\ db' = Append(db, 1)
                            /\ UNCHANGED total_size
                         \/ /\ status[self] \in {StatusReading, StatusWriting}
                            /\ status' = [status EXCEPT ![self] = StatusCompleted]
                            /\ UNCHANGED <<db, total_size>>
                      /\ pc' = [pc EXCEPT ![self] = "S"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << db, status, total_size >>

t(self) == S(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Transactions: t(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Transactions : WF_vars(t(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeOk == \A tr \in Transactions: 
                /\ status[tr] \in StatusType 
====
