A More Complex Thread
https://deadlockempire.github.io/#L1-lock

The goal of this level is not to enter the critical sections at the same time
but to reach a deadlock state.

Thread 0:
```
while (true) {
  if (Monitor.TryEnter(mutex)) {
    Monitor.Enter(mutex3);
    Monitor.Enter(mutex);
    critical_section();
    Monitor.Exit(mutex);
    Monitor.Enter(mutex2);
    flag = false;
    Monitor.Exit(mutex2);
    Monitor.Exit(mutex3);
  } else {
    Monitor.Enter(mutex2);
    flag = true;
    Monitor.Exit(mutex2);
  }
}
```
Thread 1:
```
while (true) {
  if (flag) {
    Monitor.Enter(mutex2);
    Monitor.Enter(mutex);
    flag = false;
    critical_section();
    Monitor.Exit(mutex);
    Monitor.Enter(mutex2);
  } else {
    Monitor.Enter(mutex);
    flag = false;
    Monitor.Exit(mutex);
  }
}
```


---- MODULE AMoreComplexThread ----
EXTENDS TLC, FiniteSets, Naturals, Sequences

t0 == "Thread0"
t1 == "Thread1"

(* --fair algorithm level1 {
    variables critical_section = {},
              flag = FALSE,
              mutex = <<>>,
              mutex2 = <<>>,
              mutex3 = <<>>;

define {    
    ToSet(s) == { s[i] : i \in DOMAIN s }
    TryEnter(m) == Len(m) = 0 
    Reentrant(m,id) == \/ Len(m) = 0 
                       \/ \A x \in ToSet(m) : x = id
    Last(s) == s[Len(s)]
    EXITLock(m) == SubSeq(m, 1, Len(m)-1)
}

macro ENTER(lock) {
    await Reentrant(lock, self);
    lock := Append(lock, self);
}

macro EXIT(lock) {
    assert Last(lock) = self;
    lock := EXITLock(lock);
}

fair process (p \in {t0}) {
T0:
    while (TRUE) {
T1:    if (Reentrant(mutex, t0)) {
          mutex := Append(mutex, t0);
T2:       ENTER(mutex3);    
T3:       ENTER(mutex);
T4:       critical_section := critical_section \union {t0};
T5:       critical_section := critical_section \ {t0};
T6:       EXIT(mutex);
T7:       ENTER(mutex2);
T8:       flag := FALSE;
T9:       EXIT(mutex2);
T10:      EXIT(mutex3);
       } else { 
T20:      ENTER(mutex2);
T21:      flag := TRUE;
T22:      EXIT(mutex2);
        }
    }
}

fair process (z \in {t1}) {
T30:
    while (TRUE) {
T31:   if (flag) {
T32:     ENTER(mutex2);
T33:     ENTER(mutex);
T34:     flag := FALSE;
T35:     critical_section := critical_section \union {t1};
T36:     critical_section := critical_section \ {t1};
T37:     EXIT(mutex);
T38:     ENTER(mutex2);
        } else {
T40:     ENTER(mutex);
T41:     flag := FALSE;
T42:     EXIT(mutex);
        }
    }
}

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "68a0a4fb")
VARIABLES pc, critical_section, flag, mutex, mutex2, mutex3

(* define statement *)
ToSet(s) == { s[i] : i \in DOMAIN s }
TryEnter(m) == Len(m) = 0
Reentrant(m,id) == \/ Len(m) = 0
                   \/ \A x \in ToSet(m) : x = id
Last(s) == s[Len(s)]
EXITLock(m) == SubSeq(m, 1, Len(m)-1)


vars == << pc, critical_section, flag, mutex, mutex2, mutex3 >>

ProcSet == ({t0}) \cup ({t1})

Init == (* Global variables *)
        /\ critical_section = {}
        /\ flag = FALSE
        /\ mutex = <<>>
        /\ mutex2 = <<>>
        /\ mutex3 = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in {t0} -> "T0"
                                        [] self \in {t1} -> "T29"]

T0(self) == /\ pc[self] = "T0"
            /\ pc' = [pc EXCEPT ![self] = "TIF"]
            /\ UNCHANGED << critical_section, flag, mutex, mutex2, mutex3 >>

TIF(self) == /\ pc[self] = "TIF"
             /\ IF Reentrant(mutex, t0)
                   THEN /\ mutex' = Append(mutex, t0)
                        /\ pc' = [pc EXCEPT ![self] = "T2M3"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "T20"]
                        /\ mutex' = mutex
             /\ UNCHANGED << critical_section, flag, mutex2, mutex3 >>

T2M3(self) == /\ pc[self] = "T2M3"
              /\ Reentrant(mutex3, self)
              /\ mutex3' = Append(mutex3, self)
              /\ pc' = [pc EXCEPT ![self] = "T3M"]
              /\ UNCHANGED << critical_section, flag, mutex, mutex2 >>

T3M(self) == /\ pc[self] = "T3M"
             /\ Reentrant(mutex, self)
             /\ mutex' = Append(mutex, self)
             /\ pc' = [pc EXCEPT ![self] = "T4"]
             /\ UNCHANGED << critical_section, flag, mutex2, mutex3 >>

T4(self) == /\ pc[self] = "T4"
            /\ critical_section' = (critical_section \union {t0})
            /\ pc' = [pc EXCEPT ![self] = "T5"]
            /\ UNCHANGED << flag, mutex, mutex2, mutex3 >>

T5(self) == /\ pc[self] = "T5"
            /\ critical_section' = critical_section \ {t0}
            /\ pc' = [pc EXCEPT ![self] = "T6"]
            /\ UNCHANGED << flag, mutex, mutex2, mutex3 >>

T6(self) == /\ pc[self] = "T6"
            /\ Assert(Last(mutex) = self, 
                      "Failure of assertion at line 34, column 5 of macro called at line 46, column 15.")
            /\ mutex' = EXITLock(mutex)
            /\ pc' = [pc EXCEPT ![self] = "T7"]
            /\ UNCHANGED << critical_section, flag, mutex2, mutex3 >>

T7(self) == /\ pc[self] = "T7"
            /\ Reentrant(mutex2, self)
            /\ mutex2' = Append(mutex2, self)
            /\ pc' = [pc EXCEPT ![self] = "T8"]
            /\ UNCHANGED << critical_section, flag, mutex, mutex3 >>

T8(self) == /\ pc[self] = "T8"
            /\ flag' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "T9"]
            /\ UNCHANGED << critical_section, mutex, mutex2, mutex3 >>

T9(self) == /\ pc[self] = "T9"
            /\ Assert(Last(mutex2) = self, 
                      "Failure of assertion at line 34, column 5 of macro called at line 49, column 15.")
            /\ mutex2' = EXITLock(mutex2)
            /\ pc' = [pc EXCEPT ![self] = "T10"]
            /\ UNCHANGED << critical_section, flag, mutex, mutex3 >>

T10(self) == /\ pc[self] = "T10"
             /\ Assert(Last(mutex3) = self, 
                       "Failure of assertion at line 34, column 5 of macro called at line 50, column 15.")
             /\ mutex3' = EXITLock(mutex3)
             /\ pc' = [pc EXCEPT ![self] = "T0"]
             /\ UNCHANGED << critical_section, flag, mutex, mutex2 >>

T20(self) == /\ pc[self] = "T20"
             /\ Reentrant(mutex2, self)
             /\ mutex2' = Append(mutex2, self)
             /\ pc' = [pc EXCEPT ![self] = "T21"]
             /\ UNCHANGED << critical_section, flag, mutex, mutex3 >>

T21(self) == /\ pc[self] = "T21"
             /\ flag' = TRUE
             /\ pc' = [pc EXCEPT ![self] = "T22"]
             /\ UNCHANGED << critical_section, mutex, mutex2, mutex3 >>

T22(self) == /\ pc[self] = "T22"
             /\ Assert(Last(mutex2) = self, 
                       "Failure of assertion at line 34, column 5 of macro called at line 54, column 13.")
             /\ mutex2' = EXITLock(mutex2)
             /\ pc' = [pc EXCEPT ![self] = "T0"]
             /\ UNCHANGED << critical_section, flag, mutex, mutex3 >>

p(self) == T0(self) \/ TIF(self) \/ T2M3(self) \/ T3M(self) \/ T4(self)
              \/ T5(self) \/ T6(self) \/ T7(self) \/ T8(self) \/ T9(self)
              \/ T10(self) \/ T20(self) \/ T21(self) \/ T22(self)

T29(self) == /\ pc[self] = "T29"
             /\ pc' = [pc EXCEPT ![self] = "T30"]
             /\ UNCHANGED << critical_section, flag, mutex, mutex2, mutex3 >>

T30(self) == /\ pc[self] = "T30"
             /\ IF flag
                   THEN /\ pc' = [pc EXCEPT ![self] = "T31"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "T40"]
             /\ UNCHANGED << critical_section, flag, mutex, mutex2, mutex3 >>

T31(self) == /\ pc[self] = "T31"
             /\ Reentrant(mutex2, self)
             /\ mutex2' = Append(mutex2, self)
             /\ pc' = [pc EXCEPT ![self] = "T32"]
             /\ UNCHANGED << critical_section, flag, mutex, mutex3 >>

T32(self) == /\ pc[self] = "T32"
             /\ Reentrant(mutex, self)
             /\ mutex' = Append(mutex, self)
             /\ pc' = [pc EXCEPT ![self] = "T33"]
             /\ UNCHANGED << critical_section, flag, mutex2, mutex3 >>

T33(self) == /\ pc[self] = "T33"
             /\ flag' = FALSE
             /\ pc' = [pc EXCEPT ![self] = "T34"]
             /\ UNCHANGED << critical_section, mutex, mutex2, mutex3 >>

T34(self) == /\ pc[self] = "T34"
             /\ critical_section' = (critical_section \union {t1})
             /\ pc' = [pc EXCEPT ![self] = "T35"]
             /\ UNCHANGED << flag, mutex, mutex2, mutex3 >>

T35(self) == /\ pc[self] = "T35"
             /\ critical_section' = critical_section \ {t1}
             /\ pc' = [pc EXCEPT ![self] = "T36"]
             /\ UNCHANGED << flag, mutex, mutex2, mutex3 >>

T36(self) == /\ pc[self] = "T36"
             /\ Assert(Last(mutex) = self, 
                       "Failure of assertion at line 34, column 5 of macro called at line 67, column 20.")
             /\ mutex' = EXITLock(mutex)
             /\ pc' = [pc EXCEPT ![self] = "T37_reentr"]
             /\ UNCHANGED << critical_section, flag, mutex2, mutex3 >>

T37_reentr(self) == /\ pc[self] = "T37_reentr"
                    /\ Reentrant(mutex2, self)
                    /\ mutex2' = Append(mutex2, self)
                    /\ pc' = [pc EXCEPT ![self] = "T29"]
                    /\ UNCHANGED << critical_section, flag, mutex, mutex3 >>

T40(self) == /\ pc[self] = "T40"
             /\ Reentrant(mutex, self)
             /\ mutex' = Append(mutex, self)
             /\ pc' = [pc EXCEPT ![self] = "T41"]
             /\ UNCHANGED << critical_section, flag, mutex2, mutex3 >>

T41(self) == /\ pc[self] = "T41"
             /\ flag' = FALSE
             /\ pc' = [pc EXCEPT ![self] = "T42MEXIT"]
             /\ UNCHANGED << critical_section, mutex, mutex2, mutex3 >>

T42MEXIT(self) == /\ pc[self] = "T42MEXIT"
                  /\ Assert(Last(mutex) = self, 
                            "Failure of assertion at line 34, column 5 of macro called at line 72, column 20.")
                  /\ mutex' = EXITLock(mutex)
                  /\ pc' = [pc EXCEPT ![self] = "T29"]
                  /\ UNCHANGED << critical_section, flag, mutex2, mutex3 >>

z(self) == T29(self) \/ T30(self) \/ T31(self) \/ T32(self) \/ T33(self)
              \/ T34(self) \/ T35(self) \/ T36(self) \/ T37_reentr(self)
              \/ T40(self) \/ T41(self) \/ T42MEXIT(self)

Next == (\E self \in {t0}: p(self))
           \/ (\E self \in {t1}: z(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {t0} : WF_vars(p(self))
        /\ \A self \in {t1} : WF_vars(z(self))

\* END TRANSLATION 

InfLoop == Len(mutex) < 4 
CS == ~(t0 \in critical_section /\ t1 \in critical_section)
====
