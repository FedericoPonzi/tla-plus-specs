Lamport clocks: https://lamport.azurewebsites.net/pubs/time-clocks.pdf

Mutual exclusion rules:
(I) A process which has been granted the resource must release it before it
can be granted to another process. 
(II) Different requests for the resource must be granted in the order in which
they are made. 
(III) If every process which is granted the resource eventually releases it, then every request is eventually granted.

Safety: 
    * Only a single process can access the resource at a time. Checked via assert.
Liveness:
    * All processes that requested access to the resource, eventually get it.

As we're just trying to show a way to use lamport clocks to solve a synchronization problem, 
the algorithm presented in the paper above and modeled here doesn't deal with crashes.
When the `ProcessCanFail` constant in the config to TRUE, the smallest process ("0") will never send an AckRequestResource back.
This breaks the liveness property.

---- MODULE lamport_clock ----
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Functions
LOCAL INSTANCE Folds
LOCAL INSTANCE TLC
LOCAL INSTANCE Integers

CONSTANT Processes, ProcessCanFail, MaxTimestamp
ASSUME IsFiniteSet(Processes)
ASSUME Cardinality(Processes) > 1
ASSUME \A p \in Processes : p \in Nat
ASSUME MaxTimestamp \in Nat
ASSUME ProcessCanFail \in BOOLEAN 

AckRequestResource == "AckRequestResource"
RequestResource == "RequestResource"
ReleaseResource == "ReleaseResource"
Commands == {RequestResource, AckRequestResource, ReleaseResource}
EmptyMailbox == [msg |-> "Empty"]
MessageType == [msg: Commands, proc: Processes, ts: Nat] \cup [msg: {"Empty"}]

(* --fair algorithm mutual_exclusion {

    variables resource_owner = {},
              mailbox = [p \in Processes |-> EmptyMailbox]; 

    define {
        \* Some util definitions:
        Max(x, y) == IF x > y THEN x ELSE y
        Min(x, y) == IF x > y THEN y ELSE x
        SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
        SetToSortSeq(S, op(_,_)) == SortSeq(SetToSeq(S), op)
        SeqToSet(S) == {S[d]: d \in DOMAIN S}

        CanSendMessage(myself) == \A p \in Processes : mailbox[p] = EmptyMailbox

        \* Sort function for a RequestResource message with shape <<RequestResource, pid, timestamp>>
        SortFunction(seq1, seq2) ==
            IF seq1.ts > seq2.ts
            THEN FALSE
            ELSE IF seq1.ts < seq2.ts
            THEN TRUE
            ELSE IF seq1.proc > seq2.proc
            THEN FALSE
            ELSE IF seq1.proc < seq2.proc
            THEN TRUE
            ELSE FALSE
        
        TypeLamportTimestamp(t) == t \in Nat /\ t <= MaxTimestamp

        TypeMailbox == \A m \in DOMAIN mailbox : mailbox[m] \in MessageType
        TypeResourceOwner == \A ro \in resource_owner: ro \in Processes

        \* SAFETY: Only one process is allowed in the critical section
        Inv == Cardinality(resource_owner) <= 1
    }
    \* Used for the message sending event
    macro BumpTimestamp() {
        local_timestamp := Min(local_timestamp + 1, MaxTimestamp);
    }
    \* Used for the message reciving event. We need to take max of local_timestamp and other and bump the result.
    macro BumpTimestampO(other) {
        local_timestamp := Min(Max(local_timestamp, other) + 1, MaxTimestamp);
    }

    fair process (p \in Processes)
    variables local_timestamp = 0,
              ack_request_resource = {},
              requests_queue = {};
    {
    S: 
    while (TRUE) {
        either { 
                (*********************
                    1. To request the resource, process Pi sends the message <<RequestsResource, Pi, Tm>> 
                        to every other process, and puts that message on its own request queue, where Tm is the timestamp of the message.
                **********************)
                await /\ CanSendMessage(self) 
                      /\ Cardinality(ack_request_resource) = 0;
                BumpTimestamp();
                \* append to the local requests queue
                requests_queue := requests_queue \union {[ msg |-> RequestResource, proc |-> self, ts |-> local_timestamp]};
                mailbox := [p \in Processes |-> IF p = self THEN EmptyMailbox ELSE [ msg |-> RequestResource, proc |-> self, ts |-> local_timestamp]];
                ack_request_resource := {[ msg |-> AckRequestResource, proc |-> self, ts |-> local_timestamp]};
            } or { 
                (*********************
                    2. When process Pj receives the message <<RequestsResource, Pi, Tm>> requests resource, 
                        (i) it places it on its request queue and 
                        (ii) sends a (timestamped) acknowledgment message to Pi.
                **********************)
                await mailbox[self].msg = RequestResource;
                \* Add it to the local requests queue
                requests_queue := requests_queue \union {mailbox[self]};
                \* Bump the timestamp
                BumpTimestampO(mailbox[self].ts);
                \* Respond with an Ack.

                \* buffer has space only for a message at a time
                \* so to send the ack back, we need to wait for the other process to free up their queue
                await mailbox[mailbox[self].proc] = EmptyMailbox; 
                mailbox[mailbox[self].proc] := IF ProcessCanFail /\ \A proc \in Processes \ {self}: proc > self \* if process can fail and this is the smallest
                                                THEN EmptyMailbox
                                                ELSE [ msg |-> AckRequestResource, proc |-> self, ts |-> local_timestamp];
EMPTY_MAILBOX:
                \* handling of the message is completed, release the message queue
                mailbox[self] := EmptyMailbox;
                BumpTimestamp();
            } or { 
                (*********************
                    3. Whenever Pi receives the AckRequestResource, it appends it to its local acknowledgments set.
                **********************)
                await mailbox[self].msg = AckRequestResource;
                ack_request_resource := IF /\ \E el \in ack_request_resource : mailbox[self].ts > el.ts 
                                           /\ mailbox[self].proc \notin {m.proc : m \in ack_request_resource} 
                                        THEN ack_request_resource \union {mailbox[self]} 
                                        ELSE ack_request_resource;
                \*ack_request_resource := ack_request_resource \union {mailbox[self]};
                BumpTimestampO(mailbox[self].ts);
                mailbox[self] := EmptyMailbox;
            } or {
                (*********************
                    4. To release the resource, process Pi removes any <<RequestsResource, Pi, Tm>> message from its request 
                       queue and sends a timestamped Pi, ReleaseResource message to every other process.
                **********************)
                await mailbox[self].msg = ReleaseResource;
                requests_queue := {req \in requests_queue : req.proc # mailbox[self].proc};
                BumpTimestampO(mailbox[self].ts);
                mailbox[self] := EmptyMailbox;
            } or { 
                (*********************
                    5. When process Pj receives a Pi ReleaseResource message, it removes any <<RequestsResource, Pi, Tm>> 
                       requests resource message from its request queue.
                **********************)
                await self \in resource_owner  /\ CanSendMessage(self);
                \* If there is a resource owner, its request has to be at the top of the local queue, so this is safe
                requests_queue := SeqToSet(Tail(SetToSortSeq(requests_queue, SortFunction))); 
                BumpTimestamp();
                mailbox := [p \in Processes |-> IF p = self THEN EmptyMailbox ELSE [ msg |-> ReleaseResource, proc |-> self, ts |-> local_timestamp]];
                resource_owner :=  resource_owner \ {self};
                ack_request_resource := {};
            } or { 
                (*********************
                    6. Process Pi is granted the resource when the following two conditions are satisfied: 
                        (i) There is a <<RequestsResource, Pi, Tm>> in its request queue which is ordered before any other 
                            request in its queue by the relation ⇒. (To define the relation " ⇒ " for messages, we identify a message
                            with the event of sending it.).
                        (ii) Pi has received a message from every other process timestamped later than Tm.
                **********************)
                await /\ Cardinality(requests_queue) > 0 
                    /\ Head(SetToSortSeq(requests_queue, SortFunction)).proc = self
                    /\ Cardinality(ack_request_resource) = Cardinality(Processes)
                    \* doesn't make sense to take ownership again of this resource if we already own it
                    /\ self \notin resource_owner;

                resource_owner := resource_owner \union {self};
            }
        }
    }

} 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "5aee13df")
VARIABLES resource_owner, mailbox, pc

(* define statement *)
Max(x, y) == IF x > y THEN x ELSE y
Min(x, y) == IF x > y THEN y ELSE x
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
SetToSortSeq(S, op(_,_)) == SortSeq(SetToSeq(S), op)
SeqToSet(S) == {S[d]: d \in DOMAIN S}

CanSendMessage(myself) == \A p \in Processes : mailbox[p] = EmptyMailbox


SortFunction(seq1, seq2) ==
    IF seq1.ts > seq2.ts
    THEN FALSE
    ELSE IF seq1.ts < seq2.ts
    THEN TRUE
    ELSE IF seq1.proc > seq2.proc
    THEN FALSE
    ELSE IF seq1.proc < seq2.proc
    THEN TRUE
    ELSE FALSE

TypeLamportTimestamp(t) == t \in Nat /\ t <= MaxTimestamp

TypeMailbox == \A m \in DOMAIN mailbox : mailbox[m] \in MessageType
TypeResourceOwner == \A ro \in resource_owner: ro \in Processes


Inv == Cardinality(resource_owner) <= 1

VARIABLES local_timestamp, ack_request_resource, requests_queue

vars == << resource_owner, mailbox, pc, local_timestamp, ack_request_resource, 
           requests_queue >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ resource_owner = {}
        /\ mailbox = [p \in Processes |-> EmptyMailbox]
        (* Process p *)
        /\ local_timestamp = [self \in Processes |-> 0]
        /\ ack_request_resource = [self \in Processes |-> {}]
        /\ requests_queue = [self \in Processes |-> {}]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ \/ /\ /\ CanSendMessage(self)
                    /\ Cardinality(ack_request_resource[self]) = 0
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = Min(local_timestamp[self] + 1, MaxTimestamp)]
                 /\ requests_queue' = [requests_queue EXCEPT ![self] = requests_queue[self] \union {[ msg |-> RequestResource, proc |-> self, ts |-> local_timestamp'[self]]}]
                 /\ mailbox' = [p \in Processes |-> IF p = self THEN EmptyMailbox ELSE [ msg |-> RequestResource, proc |-> self, ts |-> local_timestamp'[self]]]
                 /\ ack_request_resource' = [ack_request_resource EXCEPT ![self] = {[ msg |-> AckRequestResource, proc |-> self, ts |-> local_timestamp'[self]]}]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED resource_owner
              \/ /\ mailbox[self].msg = RequestResource
                 /\ requests_queue' = [requests_queue EXCEPT ![self] = requests_queue[self] \union {mailbox[self]}]
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = Min(Max(local_timestamp[self], (mailbox[self].ts)) + 1, MaxTimestamp)]
                 /\ mailbox[mailbox[self].proc] = EmptyMailbox
                 /\ mailbox' = [mailbox EXCEPT ![mailbox[self].proc] = IF ProcessCanFail /\ \A proc \in Processes \ {self}: proc > self
                                                                        THEN EmptyMailbox
                                                                        ELSE [ msg |-> AckRequestResource, proc |-> self, ts |-> local_timestamp'[self]]]
                 /\ pc' = [pc EXCEPT ![self] = "EMPTY_MAILBOX"]
                 /\ UNCHANGED <<resource_owner, ack_request_resource>>
              \/ /\ mailbox[self].msg = AckRequestResource
                 /\ ack_request_resource' = [ack_request_resource EXCEPT ![self] = IF  /\ \E el \in ack_request_resource[self] : mailbox[self].ts > el.ts
                                                                                       /\ mailbox[self].proc \notin {m.proc : m \in ack_request_resource[self]}
                                                                                   THEN ack_request_resource[self] \union {mailbox[self]}
                                                                                   ELSE ack_request_resource[self]]
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = Min(Max(local_timestamp[self], (mailbox[self].ts)) + 1, MaxTimestamp)]
                 /\ mailbox' = [mailbox EXCEPT ![self] = EmptyMailbox]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<resource_owner, requests_queue>>
              \/ /\ mailbox[self].msg = ReleaseResource
                 /\ requests_queue' = [requests_queue EXCEPT ![self] = {req \in requests_queue[self] : req.proc # mailbox[self].proc}]
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = Min(Max(local_timestamp[self], (mailbox[self].ts)) + 1, MaxTimestamp)]
                 /\ mailbox' = [mailbox EXCEPT ![self] = EmptyMailbox]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<resource_owner, ack_request_resource>>
              \/ /\ self \in resource_owner  /\ CanSendMessage(self)
                 /\ requests_queue' = [requests_queue EXCEPT ![self] = SeqToSet(Tail(SetToSortSeq(requests_queue[self], SortFunction)))]
                 /\ local_timestamp' = [local_timestamp EXCEPT ![self] = Min(local_timestamp[self] + 1, MaxTimestamp)]
                 /\ mailbox' = [p \in Processes |-> IF p = self THEN EmptyMailbox ELSE [ msg |-> ReleaseResource, proc |-> self, ts |-> local_timestamp'[self]]]
                 /\ resource_owner' = resource_owner \ {self}
                 /\ ack_request_resource' = [ack_request_resource EXCEPT ![self] = {}]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
              \/ /\   /\ Cardinality(requests_queue[self]) > 0
                    /\ Head(SetToSortSeq(requests_queue[self], SortFunction)).proc = self
                    /\ Cardinality(ack_request_resource[self]) = Cardinality(Processes)
                    
                    /\ self \notin resource_owner
                 /\ resource_owner' = (resource_owner \union {self})
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<mailbox, local_timestamp, ack_request_resource, requests_queue>>

EMPTY_MAILBOX(self) == /\ pc[self] = "EMPTY_MAILBOX"
                       /\ mailbox' = [mailbox EXCEPT ![self] = EmptyMailbox]
                       /\ local_timestamp' = [local_timestamp EXCEPT ![self] = Min(local_timestamp[self] + 1, MaxTimestamp)]
                       /\ pc' = [pc EXCEPT ![self] = "S"]
                       /\ UNCHANGED << resource_owner, ack_request_resource, 
                                       requests_queue >>

p(self) == S(self) \/ EMPTY_MAILBOX(self)

Next == (\E self \in Processes: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Processes : WF_vars(p(self))

\* END TRANSLATION 

TypeLocalTimestamp == \A proc \in Processes: /\ local_timestamp[proc] \in Nat
                                             /\ local_timestamp[proc] <= MaxTimestamp

TypeAckRequestResource == \A proc \in Processes: \A message \in ack_request_resource[proc]: /\ message.msg = AckRequestResource
                                                                                           /\ message.proc \in Processes
                                                                                           /\ TypeLamportTimestamp(message.ts)

TypeOk == /\ TypeMailbox
          /\ TypeResourceOwner
          /\ TypeLocalTimestamp
          /\ TypeAckRequestResource

\* LIVENESS: either we eventually get ownership, or we're at the edge of the timestamp boundary.
ResourceAcquisition == \A proc \in Processes : Cardinality(ack_request_resource[proc]) > 0 ~> \/ proc \in resource_owner 
                                                                                              \/ local_timestamp[proc] = MaxTimestamp 

====
