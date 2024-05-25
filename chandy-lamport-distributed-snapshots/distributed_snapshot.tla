Chandy-Lamport distributed snapshots protocol.
Processes do their work, and at some point any one of them can start the snapshot protocol.

---- MODULE distributed_snapshot ----
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC

CONSTANTS Processes, MaxCompMessages, MaxCompState
ASSUME IsFiniteSet(Processes)
\*ASSUME Cardinality(Processes) > 2
Marker == -2
Null == -1
ComputationStateType == Nat \union {Null}
MessageType == [sender: Processes, content: {Marker} \union Nat]


baitinv == TRUE
\*baitinv ==  TLCGet("level") < 8

(* --fair algorithm distributed_snapshot {
    \* Sequence of incoming messages, Processes[i] contains message incoming for Process i.
    variables channels = [receiver \in Processes |-> <<>>];
    define {
        IsNotEmpty(ch) == Len(ch) > 0
        IsEmpty(ch) == ~IsNotEmpty(ch)
        LastMessage(p) == Head(channels[p])
        LastMessageIsMarker(p) == /\ IsNotEmpty(channels[p])
                                  /\ ~ LastMessage(p).content \in Nat 
                                  /\ LastMessage(p).content = Marker
        ConsumeLastMessage(p) == [proc \in (Processes \intersect {p}) |-> Tail(channels[proc])] @@ channels
        IsRecording(state) == state["computation"] # Null
        SendMessage(p, msg) == [receiver \in (Processes \ {p}) |-> Append(channels[receiver], [sender |-> p, content |-> msg])] @@ channels
        SendMarkerMessage(p) == SendMessage(p, Marker)
        Last(seq) ==  seq[Len(seq)]
        AppendMessageToRecording(chans, sender, msg) == [p \in Processes \intersect {sender} |-> Append(chans[sender], msg)]
        StoreMessageInSnapshot(p, stateChans) == [chans |-> AppendMessageToRecording(stateChans, LastMessage(p).sender, LastMessage(p).content) @@ stateChans] 
        \* Channel recording is closed when the last message in the snapshot for that channel is a Marker.
        ChannelRecordingIsOngoing(p, stateChans) == /\ IsNotEmpty(stateChans[LastMessage(p).sender]) 
                                                     /\ Last(stateChans[LastMessage(p).sender]) = Marker
    }
 
   fair process (p \in Processes)
    variables computation = 0, 
              compMsgSent = 0,
              snapshot = [computation |-> Null, chans |-> [p \in Processes \ {self} |-> <<>>]];
    {
S:
        while (TRUE) {
            either {
                \* Generate some sample state and exchange messages
                \* Proceed with the local computation
                computation := computation + 1;
            } or {
                \* Send a computation related message
                \* This could be sent at any point during the life of the process.
                computation := computation + 1;
                \* used to limit the number of outgoing messages
                compMsgSent := compMsgSent + 1;

                channels := SendMessage(self, computation);
            } or {
                \* Check if we received a message (other than the marker)
                \* And we're not recording the channel messages
                await /\ IsNotEmpty(channels[self]) 
                      /\ ~ LastMessageIsMarker(self)
                      /\ ~ IsRecording(snapshot);
                channels := ConsumeLastMessage(self);
                computation := computation + 1;
            } or {
                \* Check if we received a message and are in recording mode.
                await /\ IsNotEmpty(channels[self]) 
                      /\ IsRecording(snapshot)
                      /\ \/ IsEmpty(snapshot["chans"][LastMessage(self).sender])
                         \/ ChannelRecordingIsOngoing(self, snapshot["chans"]);
                \* Store the message:
                snapshot := StoreMessageInSnapshot(self, snapshot["chans"]) @@ snapshot;
                channels := ConsumeLastMessage(self);

            } or { \* Snapshot protocol below!
                \* decided to start snapshot protocol. It should not restart if it already have stored a snapshot
                await ~IsRecording(snapshot);
                snapshot := [computation |-> computation] @@ snapshot;
                \* send a marker message to all outgoing channels.
                channels := SendMarkerMessage(self);
            } or {
                \* Check if we received our first marker message
                await /\ LastMessageIsMarker(self) 
                      /\ ~IsRecording(snapshot);
                
                \* remove the marker
                channels := ConsumeLastMessage(self);
                \* Start recording and store the marker message in the queue for this sender
                snapshot := [computation |-> computation] @@ StoreMessageInSnapshot(self, snapshot["chans"]);
SNAP_MARKER_SND:
                \* send a message to all outgoing channels.
                channels := SendMarkerMessage(self);
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "dbf3805e")
VARIABLES channels, pc

(* define statement *)
IsNotEmpty(ch) == Len(ch) > 0
IsEmpty(ch) == ~IsNotEmpty(ch)
LastMessage(p) == Head(channels[p])
LastMessageIsMarker(p) == /\ IsNotEmpty(channels[p])
                          /\ ~ LastMessage(p).content \in Nat
                          /\ LastMessage(p).content = Marker
ConsumeLastMessage(p) == [proc \in (Processes \intersect {p}) |-> Tail(channels[proc])] @@ channels
IsRecording(state) == state["computation"] # Null
SendMessage(p, msg) == [receiver \in (Processes \ {p}) |-> Append(channels[receiver], [sender |-> p, content |-> msg])] @@ channels
SendMarkerMessage(p) == SendMessage(p, Marker)
Last(seq) ==  seq[Len(seq)]
AppendMessageToRecording(chans, sender, msg) == [p \in Processes \intersect {sender} |-> Append(chans[sender], msg)]
StoreMessageInSnapshot(p, stateChans) == [chans |-> AppendMessageToRecording(stateChans, LastMessage(p).sender, LastMessage(p).content) @@ stateChans]

ChannelRecordingIsOngoing(p, stateChans) == /\ IsNotEmpty(stateChans[LastMessage(p).sender])
                                             /\ Last(stateChans[LastMessage(p).sender]) = Marker

VARIABLES computation, compMsgSent, snapshot

vars == << channels, pc, computation, compMsgSent, snapshot >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ channels = [receiver \in Processes |-> <<>>]
        (* Process p *)
        /\ computation = [self \in Processes |-> 0]
        /\ compMsgSent = [self \in Processes |-> 0]
        /\ snapshot = [self \in Processes |-> [computation |-> Null, chans |-> [p \in Processes \ {self} |-> <<>>]]]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ \/ /\ computation' = [computation EXCEPT ![self] = computation[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<channels, compMsgSent, snapshot>>
              \/ /\ computation' = [computation EXCEPT ![self] = computation[self] + 1]
                 /\ compMsgSent' = [compMsgSent EXCEPT ![self] = compMsgSent[self] + 1]
                 /\ channels' = SendMessage(self, computation'[self])
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED snapshot
              \/ /\ /\ IsNotEmpty(channels[self])
                    /\ ~ LastMessageIsMarker(self)
                    /\ ~ IsRecording(snapshot[self])
                 /\ channels' = ConsumeLastMessage(self)
                 /\ computation' = [computation EXCEPT ![self] = computation[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<compMsgSent, snapshot>>
              \/ /\ /\ IsNotEmpty(channels[self])
                    /\ IsRecording(snapshot[self])
                    /\ \/ IsEmpty(snapshot[self]["chans"][LastMessage(self).sender])
                       \/ ChannelRecordingIsOngoing(self, snapshot[self]["chans"])
                 /\ snapshot' = [snapshot EXCEPT ![self] = StoreMessageInSnapshot(self, snapshot[self]["chans"]) @@ snapshot[self]]
                 /\ channels' = ConsumeLastMessage(self)
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<computation, compMsgSent>>
              \/ /\ ~IsRecording(snapshot[self])
                 /\ snapshot' = [snapshot EXCEPT ![self] = [computation |-> computation[self]] @@ snapshot[self]]
                 /\ channels' = SendMarkerMessage(self)
                 /\ pc' = [pc EXCEPT ![self] = "S"]
                 /\ UNCHANGED <<computation, compMsgSent>>
              \/ /\ /\ LastMessageIsMarker(self)
                    /\ ~IsRecording(snapshot[self])
                 /\ channels' = ConsumeLastMessage(self)
                 /\ snapshot' = [snapshot EXCEPT ![self] = [computation |-> computation[self]] @@ StoreMessageInSnapshot(self, snapshot[self]["chans"])]
                 /\ pc' = [pc EXCEPT ![self] = "SNAP_MARKER_SND"]
                 /\ UNCHANGED <<computation, compMsgSent>>

SNAP_MARKER_SND(self) == /\ pc[self] = "SNAP_MARKER_SND"
                         /\ channels' = SendMarkerMessage(self)
                         /\ pc' = [pc EXCEPT ![self] = "S"]
                         /\ UNCHANGED << computation, compMsgSent, snapshot >>

p(self) == S(self) \/ SNAP_MARKER_SND(self)

Next == (\E self \in Processes: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Processes : WF_vars(p(self))

\* END TRANSLATION 


TypeOk == /\ Cardinality(DOMAIN channels) = Cardinality(Processes)
          /\ \A proc \in DOMAIN channels: 
                \A msg \in DOMAIN channels[proc]: 
                    channels[proc][msg] \in MessageType
          /\ \A proc \in DOMAIN snapshot: 
                snapshot[proc]["computation"] \in ComputationStateType
          /\ \A proc \in DOMAIN snapshot: 
                \A sender \in DOMAIN snapshot[proc]["chans"]: 
                    \A recording \in DOMAIN snapshot[proc]["chans"][sender]: 
                        snapshot[proc]["chans"][sender][recording] \in (Nat \union {Marker})

Inv == baitinv

EveryChannelIsRecorded == \A proc \in Processes: 
                            \A sender \in Processes \ {proc}: 
                                /\ IsNotEmpty(snapshot[proc]["chans"][sender]) 
                                /\ Last(snapshot[proc]["chans"][sender]) = Marker
EveryStateIsRecorded == \A proc \in Processes: 
                            snapshot[proc]["computation"] # Null

\* If snapshot is taken anywhere, eventually every state is recorded and every channel is recorded up to the first Marker msg.
Snapshot == <>[] \E proc \in DOMAIN snapshot: 
                snapshot[proc]["computation"] # Null => /\ EveryStateIsRecorded 
                                                        /\ EveryChannelIsRecorded
\* Any message that is sent by a process before recording its snapshot, 
\* must be recorded in the global snapshot
ConsistentGlobalStateCondition1 == \A proc \in DOMAIN snapshot:
                                       \A receiver \in DOMAIN snapshot[proc]["chans"]:
                                            \A recordedMessage \in DOMAIN snapshot[proc]["chans"][receiver]:
                                                snapshot[proc]["chans"][receiver][recordedMessage] < snapshot[proc]["computation"]


\* Any message that is sent by a process after recording its snapshot,
\* must not be recorded in the global snapshot
ConsistentGlobalStateCondition2 == \A procSnapshot \in DOMAIN snapshot:
                                        snapshot[procSnapshot]["computation"] # Null => \A proc \in DOMAIN channels:
                                            \A msg \in DOMAIN channels[proc]:                                        
                                                channels[proc][msg]["sender"] = procSnapshot => 
                                                    \/ channels[proc][msg]["content"] = Marker
                                                    \/ snapshot[procSnapshot]["computation"] < channels[proc][msg]["content"]

ConsistentGlobalState == /\ ConsistentGlobalStateCondition1 
                         /\ ConsistentGlobalStateCondition2

\* State constraint to keep the model bounded
MaxCompMessagesConstraint == \A proc \in Processes: compMsgSent[proc] < MaxCompMessages
MaxCompStateConstraint == \A proc \in Processes: computation[proc] < MaxCompState
====


