A lease can be thought as a lock with a timeout. When a process holds a loc, it can access some resources.
In case the lock owner dies, to avoid deadlock the lock has a fixed timeout time.
If the lease is not renewed before the lease is expired (or explicitly released), a new process can attempt to acquire the lease.
Sometimes it get implemented like this:

1. while TRUE {
2.     if (leaseAlmostOver()){
3.         renewLease();
4.     }
5.     doOperationOnResource()
6. }

This code introduces a Time Of Check/ Time Of Use Bug (TOCTOU) on line 5. 
After the lease is renewed, the lease owner could potentially be put to sleep for an 
amount of time greater than the reaming lease time. 
After waking up, the process would start the operation assuming he still 
holds the lease which instead has since expired while the lease was since acquired by another process.

One solution would be to use atomic commit, and check at the end if the lease is still valid.

This specification models the above algorithm to expose the concurrency bug.

The available states are:
* WaitingForLease - Initial. When the process doesn't own a lock.
* RenewedLease - maps to line 3.
* DoingOperation - maps to line 4. 
* Sleep - maps to the concept of sleep and expired lease.

The invariant offered by a lease is similar to locks: only a single process can access the 
critical section at a time. To verify this, we assume that a process will 
not get a lease if we know it's already holded by another process. When the owner goes 
to the sleep state, we assume it goes to sleep for enough time that the lease is expired. 
This allows us to avoid dealing with the time variable.

References:
    * Designing Data Intensive Systems, chapter 8 section "Process Pauses"
    * https://martin.kleppmann.com/2016/02/08/how-to-do-distributed-locking.html

------------------------- MODULE lease -------------------------
EXTENDS Integers, TLC, FiniteSets

CONSTANTS Workers


StatesSleep == "Sleep"
StatesWaitingLease == "WaitingLease"
StatesDoingOperation == "DoingOperation"
StatesRenewedLease == "RenewedLease"
States == {StatesSleep, StatesWaitingLease, StatesDoingOperation, StatesRenewedLease}

\*baitinv == TLCGet("level") < 16

(* --algorithm leaseVerifier {
    variables states = [x \in Workers |-> StatesWaitingLease];
    define {
        OnlyOneLeader == Cardinality({w \in DOMAIN (states): states[w] = StatesDoingOperation}) <= 1
        TypeOk == \A w \in Workers: states[w] \in States
        Inv == /\ TypeOk
               /\ OnlyOneLeader
               \*/\ baitinv 
    }

    macro stateIs(s) {
        states[self] = s
    }

    process (w \in Workers) {
W:
        while(TRUE) {
            either {
                \* If lease is expired, renew
                await stateIs(StatesWaitingLease)
                await ~\E w \in Workers : states[w] = StatesDoingOperation \/ states[w] = StatesRenewedLease;
                states[self] := StatesRenewedLease;
            } or {
                \* Leader goes to sleep before start operation
                await stateIs(StatesRenewedLease);
                \* this state is like saying that lease is expired.
                states[self] := StatesSleep;
            } or {
                \* Leader start the operation
                await stateIs(StatesRenewedLease) \/ stateIs(StatesSleep);
                states[self] := StatesDoingOperation;
            } or {
                \* Leader has completed the operation, no goes through the renew lease phase.
                await stateIs(StatesDoingOperation);
                states[self] := StatesWaitingLease;
            }
        }
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "92808600" /\ chksum(tla) = "8f5050cf")
VARIABLE states

(* define statement *)
OnlyOneLeader == Cardinality({w \in DOMAIN (states): states[w] = StatesDoingOperation}) <= 1

TypeOk == \A w \in Workers: states[w] \in States
Inv == /\ TypeOk
       /\ OnlyOneLeader


vars == << states >>

ProcSet == (Workers)

Init == (* Global variables *)
        /\ states = [x \in Workers |-> StatesWaitingLease]

w(self) == \/ /\ states[self] = StatesWaitingLease
              /\ ~\E w \in Workers : states[w] = StatesDoingOperation \/ states[w] = StatesRenewedLease
              /\ states' = [states EXCEPT ![self] = StatesRenewedLease]
           \/ /\ states[self] = StatesRenewedLease
              /\ states' = [states EXCEPT ![self] = StatesSleep]
           \/ /\ states[self] = StatesRenewedLease \/ states[self] = StatesSleep
              /\ states' = [states EXCEPT ![self] = StatesDoingOperation]
           \/ /\ states[self] = StatesDoingOperation
              /\ states' = [states EXCEPT ![self] = StatesWaitingLease]

Next == (\E self \in Workers: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 




===========================================

