Lamport clocks: https://lamport.azurewebsites.net/pubs/time-clocks.pdf

Mutual exclusion
(I) A process which has been granted the resource must release it before it
can be granted to another process. 
(II) Different requests for the resource must be granted in the order in which
they are made. 
(III) If every process which is granted the resource eventually releases it, then every request is eventually granted.

todo: failure:
> A process must know all the commands issued by other processes, so
> that the failure of a single process will make it impossible
> for any other process to execute State Machine com-
> mands, thereby halting the system.


---- MODULE lamport_clock ----
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Functions
LOCAL INSTANCE Folds
LOCAL INSTANCE TLC
LOCAL INSTANCE Integers

CONSTANT Processes
ASSUME \A p \in Processes : p \in Nat
AckRequestResource == "AckRequestResource"
RequestResource == "RequestResource"
ReleaseResource == "ReleaseResource"
Commands == {RequestResource, AckRequestResource, ReleaseResource}
EmptyMailbox == <<"Empty">>

baitinv == TRUE
\*baitinv ==  TLCGet("level") < 30

(* --fair algorithm mutual_exclusion{

    variables resource_owner = -1,
              mailbox = [p \in Processes |-> EmptyMailbox],
              resource_owner_history = [p \in Processes |-> 0]; 

    define {
        Max(x, y) == IF x > y THEN x ELSE y
        CanSendMessage(myself) == \A p \in Processes : mailbox[p] = EmptyMailbox
        \* has the shape: <<"EmptyMailbox"> | <<Command, process, timestamp>>
        TypeMailbox == \/ \A m \in DOMAIN mailbox : mailbox[m] = EmptyMailbox 
                       \/ \A m \in DOMAIN mailbox : /\ mailbox[m][1] \in Commands
                                                    /\ mailbox[m][2] \in Processes 
                                                    /\ mailbox[m][3] \in Nat
 
        TypeOk == /\ IsFiniteSet(Processes)
                  /\ TypeMailbox         
        
        SetToSeq(S) == 
            CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
        SetToSortSeq(S, op(_,_)) ==
            SortSeq(SetToSeq(S), op)
        SeqToSet(S) == {S[d]: d \in DOMAIN S}
        \* Sort function for a RequestResource message with shape <<RequestResource, pid, timestamp>>
        SortFunction(seq1, seq2) ==
            IF seq1[3] > seq2[3]
            THEN FALSE
            ELSE IF seq1[3] < seq2[3]
            THEN TRUE
            ELSE IF seq1[2] > seq2[2]
            THEN FALSE
            ELSE IF seq1[2] < seq2[2]
            THEN TRUE
            ELSE FALSE

        \* everyone eventually get access to the resource
        Inv ==  ~ (\A p \in Processes : resource_owner_history[p] > 0)
    }
    \* Used for the message sending event
    macro BumpTimestamp() {
        local_timestamp := local_timestamp + 1;
    }
    \* Used for the message reciving event. We need to take max of local_timestamp and other and bump the result.
    macro BumpTimestampO(other) {
        local_timestamp := Max(local_timestamp, other) + 1;
    }
    macro SendRequestResourceMessage() {
        await /\ resource_owner = -1 
              /\ CanSendMessage(self) 
              /\ Cardinality(ack_request_resource) = 0;
        BumpTimestamp();
        \* append to the local requests queue
        requests_queue := requests_queue \union {<<RequestResource, self, local_timestamp>>};
        mailbox := [p \in Processes |-> IF p = self THEN EmptyMailbox ELSE <<RequestResource,self, local_timestamp>>];
        ack_request_resource := {<<AckRequestResource, self, local_timestamp>>};
    }

    macro HandleReleaseResourceMessage() {
        await mailbox[self][1] = ReleaseResource;
        requests_queue := {req \in requests_queue : req[2] # mailbox[self][2]};
        BumpTimestampO(mailbox[self][3]);
        mailbox[self] := EmptyMailbox;
    }

    macro ReleaseResourceOwnership () {
        await resource_owner = self /\ CanSendMessage(self);
        \* If we're the resource owner it means we're at the top of the local queue, so it should work
        requests_queue := SeqToSet(Tail(SetToSortSeq(requests_queue, SortFunction))); 
        BumpTimestamp();
        mailbox := [p \in Processes |-> IF p = self THEN EmptyMailbox ELSE <<ReleaseResource, self, local_timestamp>>];
        resource_owner := -1;
        ack_request_resource := {};
    }
    macro TakeOwnership() {
        await /\ Cardinality(requests_queue) > 0 
              /\ Head(SetToSortSeq(requests_queue, SortFunction))[2] = self
              /\ Cardinality(ack_request_resource) = Cardinality(Processes)
              \* doesn't make sense to take ownership again of this resource if we already own it
              /\ resource_owner # self;

        assert resource_owner = -1;
        resource_owner_history[self] := resource_owner_history[self] + 1;
        resource_owner := self;
    }

    macro HandleAckRequestResourceMessage() {
        \* handle an AckRequestResource message
        await mailbox[self][1] = AckRequestResource;
        ack_request_resource := IF  /\ \E el \in ack_request_resource : mailbox[self][3] > el[3] 
                                    /\ mailbox[self][2] \notin {m[2] : m \in ack_request_resource} 
                                THEN ack_request_resource \union {mailbox[self]} 
                                ELSE ack_request_resource;
        BumpTimestampO(mailbox[self][3]);
        mailbox[self] := EmptyMailbox;
    }

    fair process (p \in Processes)
    variables local_timestamp = 0,
              ack_request_resource = {},
              requests_queue = {};
    {
    S: 
        while (TRUE) {
            either { \* send a request resource message
                SendRequestResourceMessage();
            } or { 
                \* Handle a request resource message by 1. adding it to the local requests_queue and 2. sending a timestampated ack back
                \* message being <<MessageType, Process, timestamp>>
                await mailbox[self][1] = RequestResource;
                \* Add it to the local requests queue
                requests_queue := requests_queue \union  {mailbox[self]};
                \* Bump the timestamp
                BumpTimestampO(mailbox[self][3]);
                \* Respond with an Ack.

                \* buffer has space only for a message at a time
                \* so to send the ack back, we need to wait for the other process to free up their queue
                await mailbox[mailbox[self][2]] = EmptyMailbox; 
                mailbox[mailbox[self][2]] := <<AckRequestResource, self, local_timestamp>>;
EMPTY_MAILBOX:
                \* handle of the message is completed, release the message queue
                mailbox[self] := EmptyMailbox;
                BumpTimestamp();
            } or {
                \* When process Pj receives a Pi releases resource
                \* message, it removes any Tm:P~ requests resource message
                \* from its request queue.
                HandleReleaseResourceMessage();
            } or {
                \* To release the resource, process P~ removes any
                \* Tm:Pi requests resource message from its request queue
                \* and sends a (timestamped) Pi releases resource message
                \* to every other process.
                ReleaseResourceOwnership();
            } or {
                \* take owenrship if possible
                TakeOwnership();
            } or {
                HandleAckRequestResourceMessage();
            }
        }
    }

} 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "20e09a51")
VARIABLES resource_owner, mailbox, resource_owner_history, pc

(* define statement *)
Max(x, y) == IF x > y THEN x ELSE y
CanSendMessage(myself) == \A p \in Processes : mailbox[p] = EmptyMailbox

TypeMailbox == \/ mailbox = EmptyMailbox
               \/ \A m \in DOMAIN mailbox : /\ mailbox[m][1] \in Commands
                                            /\ mailbox[m][2] \in Processes
                                            /\ mailbox[m][3] \in Nat

TypeOk == /\ IsFiniteSet(Processes)
          /\ TypeMailbox

SetToSeq(S) ==
    CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
SetToSortSeq(S, op(_,_)) ==
    SortSeq(SetToSeq(S), op)
SeqToSet(S) == {S[d]: d \in DOMAIN S}

SortFunction(seq1, seq2) ==
    IF seq1[3] > seq2[3]
    THEN FALSE
    ELSE IF seq1[3] < seq2[3]
    THEN TRUE
    ELSE IF seq1[2] > seq2[2]
    THEN FALSE
    ELSE IF seq1[2] < seq2[2]
    THEN TRUE
    ELSE FALSE


Inv ==  ~ (\A p \in Processes : resource_owner_history[p] > 0)

VARIABLES local_timestamp, ack_request_resource, requests_queue

vars == << resource_owner, mailbox, resource_owner_history, pc, 
           local_timestamp, ack_request_resource, requests_queue >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ resource_owner = -1
        /\ mailbox = [p \in Processes |-> EmptyMailbox]
        /\ resource_owner_history = [p \in Processes |-> 0]
        (* Process p *)
        /\ local_timestamp = [self \in Processes |-> 0]
        /\ ack_request_resource = [self \in Processes |-> {}]
        /\ requests_queue = [self \in Processes |-> {}]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ \/ /\ /\ resource_owner = -1
                    /\ CanSendMessage(self)
                    /\ Cardinality(ack_request_resource[self]) = 0
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = local_timestamp[self] + 1]
                 /\ requests_queue' = [requests_queue EXCEPT ![self] = requests_queue[self] \union {<<RequestResource, self, local_timestamp'[self]>>}]
                 /\ mailbox' = [p \in Processes |-> IF p = self THEN EmptyMailbox ELSE <<RequestResource,self, local_timestamp'[self]>>]
                 /\ ack_request_resource' = [ack_request_resource EXCEPT ![self] = {<<AckRequestResource, self, local_timestamp'[self]>>}]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<resource_owner, resource_owner_history>>
              \/ /\ mailbox[self][1] = RequestResource
                 /\ requests_queue' = [requests_queue EXCEPT ![self] = requests_queue[self] \union  {mailbox[self]}]
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = Max(local_timestamp[self], (mailbox[self][3])) + 1]
                 /\ mailbox[mailbox[self][2]] = EmptyMailbox
                 /\ mailbox' = [mailbox EXCEPT ![mailbox[self][2]] = <<AckRequestResource, self, local_timestamp'[self]>>]
                 /\ pc' = [pc EXCEPT ![self] = "EMPTY_MAILBOX"]
                 /\ UNCHANGED <<resource_owner, resource_owner_history, ack_request_resource>>
              \/ /\ mailbox[self][1] = ReleaseResource
                 /\ requests_queue' = [requests_queue EXCEPT ![self] = {req \in requests_queue[self] : req[2] # mailbox[self][2]}]
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = Max(local_timestamp[self], (mailbox[self][3])) + 1]
                 /\ mailbox' = [mailbox EXCEPT ![self] = EmptyMailbox]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<resource_owner, resource_owner_history, ack_request_resource>>
              \/ /\ resource_owner = self /\ CanSendMessage(self)
                 /\ requests_queue' = [requests_queue EXCEPT ![self] = SeqToSet(Tail(SetToSortSeq(requests_queue[self], SortFunction)))]
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = local_timestamp[self] + 1]
                 /\ mailbox' = [p \in Processes |-> IF p = self THEN EmptyMailbox ELSE <<ReleaseResource, self, local_timestamp'[self]>>]
                 /\ resource_owner' = -1
                 /\ ack_request_resource' = [ack_request_resource EXCEPT ![self] = {}]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED resource_owner_history
              \/ /\ /\ Cardinality(requests_queue[self]) > 0
                    /\ Head(SetToSortSeq(requests_queue[self], SortFunction))[2] = self
                    /\ Cardinality(ack_request_resource[self]) = Cardinality(Processes)
                    
                    /\ resource_owner # self
                 /\ Assert(resource_owner = -1, 
                           "Failure of assertion at line 117, column 9 of macro called at line 173, column 17.")
                 /\ resource_owner_history' = [resource_owner_history EXCEPT ![self] = resource_owner_history[self] + 1]
                 /\ resource_owner' = self
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<mailbox, local_timestamp, ack_request_resource, requests_queue>>
              \/ /\ mailbox[self][1] = AckRequestResource
                 /\ ack_request_resource' = [ack_request_resource EXCEPT ![self] = IF  /\ \E el \in ack_request_resource[self] : mailbox[self][3] > el[3]
                                                                                       /\ mailbox[self][2] \notin {m[2] : m \in ack_request_resource[self]}
                                                                                   THEN ack_request_resource[self] \union {mailbox[self]}
                                                                                   ELSE ack_request_resource[self]]
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = Max(local_timestamp[self], (mailbox[self][3])) + 1]
                 /\ mailbox' = [mailbox EXCEPT ![self] = EmptyMailbox]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<resource_owner, resource_owner_history, requests_queue>>

EMPTY_MAILBOX(self) == /\ pc[self] = "EMPTY_MAILBOX"
                       /\ mailbox' = [mailbox EXCEPT ![self] = EmptyMailbox]
                       /\ local_timestamp' = [local_timestamp EXCEPT ![self] = local_timestamp[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "S"]
                       /\ UNCHANGED << resource_owner, resource_owner_history, 
                                       ack_request_resource, requests_queue >>

p(self) == S(self) \/ EMPTY_MAILBOX(self)

Next == (\E self \in Processes: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Processes : WF_vars(p(self))

\* END TRANSLATION 


====
