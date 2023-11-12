This code is from the talk SREcon20 Americas - Weeks of Debugging Can Save You Hours of TLA+ by Markus A. Kuppe.
https://www.youtube.com/watch?v=wjsI0lTSjIo


void *producer(void * arg) {
    while(1) {
        pthread_mutex_lock(&mutex); // acquire the lock
        while(count == buff_size) // check if the buffer is full
            pthread_cond_wait(&modify, &mutex);
        append(rand() % (10)); // produce!
            
        pthread_cond_signal(&modify); // broadcast that the buffer is full
        pthread_mutex_unlock(&mutex); // release the lock
    }
}

void *consumer(void * arg) {
    long report = 0;
    while(1) {
        pthread_mutex_lock(&mutex); // acquire the lock

        while(count == 0) // check if the buffer is empty
            pthread_cond_wait(&modify, &mutex); // wait for the buffer

        head(); // consume (we don't care about the value)
        pthread_cond_signal(&modify); // signal that the buffer is empty
        pthread_mutex_unlock(&mutex); // release the lock
            
        if (report++ % 10000 == 0) {
            printf("\n%ld values consumed", report);
        }
    }
}

It contains some concurrency bug, the goal of this spec is to spot it.

---- MODULE weeks_of_debugging ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANT BufferSize, Producers, Consumers
\*baitinv == TRUE
baitinv ==  TLCGet("level") < 11

empty == 10

(* --algorithm weeks_of_debugging {
    variables mutex = empty, buffer = 0;
    define {
        TypeOk == /\ buffer >= 0 /\ buffer <= BufferSize
        IsBufferFull == buffer = BufferSize
        IsBufferEmpty == buffer = 0
    }
    fair process (prod \in Producers) {
PROD:
        while(TRUE) {
            await mutex = empty;
            mutex := self;
PROD1:
            while(IsBufferFull) {
                mutex := empty;
PROD3:
                await mutex = empty;
                mutex := self;
            };
PRODUCING:
            buffer := buffer +1;
            mutex := empty;
        }
    }

    fair process (cons \in Consumers) {
CONS:
        while(TRUE) {
            await mutex = empty;
            mutex := self;
CONS1:
            while(IsBufferEmpty) {
                mutex := empty;
CONS3:
                await mutex = empty;
                mutex := self;
            };
CONSUMING:
            buffer := buffer -1;
            mutex := empty;
        }
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "4ecf8bc0" /\ chksum(tla) = "d8157b85")
VARIABLES mutex, buffer, pc

(* define statement *)
TypeOk == /\ buffer >= 0 /\ buffer <= BufferSize
IsBufferFull == buffer = BufferSize
IsBufferEmpty == buffer = 0


vars == << mutex, buffer, pc >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ mutex = empty
        /\ buffer = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "PROD"
                                        [] self \in Consumers -> "CONS"]

PROD(self) == /\ pc[self] = "PROD"
              /\ mutex = empty
              /\ mutex' = self
              /\ pc' = [pc EXCEPT ![self] = "PROD1"]
              /\ UNCHANGED buffer

PROD1(self) == /\ pc[self] = "PROD1"
               /\ IF IsBufferFull
                     THEN /\ mutex' = empty
                          /\ pc' = [pc EXCEPT ![self] = "PROD3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "PRODUCING"]
                          /\ mutex' = mutex
               /\ UNCHANGED buffer

PROD3(self) == /\ pc[self] = "PROD3"
               /\ mutex = empty
               /\ mutex' = self
               /\ pc' = [pc EXCEPT ![self] = "PROD1"]
               /\ UNCHANGED buffer

PRODUCING(self) == /\ pc[self] = "PRODUCING"
                   /\ buffer' = buffer +1
                   /\ mutex' = empty
                   /\ pc' = [pc EXCEPT ![self] = "PROD"]

prod(self) == PROD(self) \/ PROD1(self) \/ PROD3(self) \/ PRODUCING(self)

CONS(self) == /\ pc[self] = "CONS"
              /\ mutex = empty
              /\ mutex' = self
              /\ pc' = [pc EXCEPT ![self] = "CONS1"]
              /\ UNCHANGED buffer

CONS1(self) == /\ pc[self] = "CONS1"
               /\ IF IsBufferEmpty
                     THEN /\ mutex' = empty
                          /\ pc' = [pc EXCEPT ![self] = "CONS3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "CONSUMING"]
                          /\ mutex' = mutex
               /\ UNCHANGED buffer

CONS3(self) == /\ pc[self] = "CONS3"
               /\ mutex = empty
               /\ mutex' = self
               /\ pc' = [pc EXCEPT ![self] = "CONS1"]
               /\ UNCHANGED buffer

CONSUMING(self) == /\ pc[self] = "CONSUMING"
                   /\ buffer' = buffer -1
                   /\ mutex' = empty
                   /\ pc' = [pc EXCEPT ![self] = "CONS"]

cons(self) == CONS(self) \/ CONS1(self) \/ CONS3(self) \/ CONSUMING(self)

Next == (\E self \in Producers: prod(self))
           \/ (\E self \in Consumers: cons(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Producers : WF_vars(prod(self))
        /\ \A self \in Consumers : WF_vars(cons(self))

\* END TRANSLATION 


====

