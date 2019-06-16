--------------------------- MODULE slidingSender ---------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANTS MESSAGE, WINDOW_SIZE, Corruption
ASSUME WINDOW_SIZE \in 0..99


(*--algorithm SlidingSender
variables
    slidingIdx = 1,
    outputWire = <<>>,
    inputWire = <<>>,
    state = "WAITING";
define

RECURSIVE getPackets2(_,_,_)

\*This converts the input at index into packets
getPackets(input,idx) == getPackets2(input, idx, WINDOW_SIZE)
\*
getPackets2(input, idx, size) == IF idx > Len(input) \/ size = 0
                                 THEN <<>>
                                 ELSE << <<idx, input[idx]>> >> \o getPackets2(input, idx+1, size-1)
end define

fair process ReceiveSyn = "SynAck"
begin A:
while state = "WAITING" do
    await inputWire # <<>>;
    if inputWire[1] # Corruption then
        state := "OPENING"
    end if;
    inputWire := <<>>;
end while;
end process;

fair process SendSynAck = "SendSynAck"
begin A:
while TRUE do
    await state = "OPENING" /\ outputWire = <<>>;
    outputWire := <<<<0, "SYNACK">>>>;
end while;
end process;

fair process ReceiveFirstAck = "ReceiveButFirst"
begin A:
while TRUE do
    await state = "OPENING" /\ inputWire # <<>>;
    if Head(inputWire) # Corruption /\ Head(inputWire)[1] = "ACK" /\ Head(inputWire)[2] = slidingIdx then
        state := "OPEN";
    else
        print(inputWire);
    end if;
    inputWire := Tail(inputWire);
end while;
end process;

fair process sendWindow = "Sender"
begin A:
while TRUE do
    \*toSend
    await /\ outputWire = <<>>
          /\ slidingIdx <= Len(MESSAGE)
          /\ state = "OPEN";
    outputWire := getPackets(MESSAGE, slidingIdx);
end while;
end process;

fair process receiveLatest = "ACK"
begin A:
while TRUE do
    await /\ inputWire # <<>>
          /\ state = "OPEN";
    if Head(inputWire) # Corruption /\ Head(inputWire)[2] >= slidingIdx then
        slidingIdx := Head(inputWire)[2] + 1;
    end if;
    inputWire := Tail(inputWire);
end while;
end process;

\*fair process timeOut = "Time Out"
\*begin A:
\*await /\ outputWire = <<>>
\*      /\ slidingIdx >= Len(MESSAGE) + 1
\*      /\ ~timeOut;
\*timeOut := TRUE;
\*end process;

end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process ReceiveSyn at line 27 col 1 changed to A_
\* Label A of process SendSynAck at line 38 col 1 changed to A_S
\* Label A of process ReceiveFirstAck at line 46 col 1 changed to A_R
\* Label A of process sendWindow at line 59 col 1 changed to A_s
VARIABLES slidingIdx, outputWire, inputWire, state, pc

(* define statement *)
RECURSIVE getPackets2(_,_,_)


getPackets(input,idx) == getPackets2(input, idx, WINDOW_SIZE)

getPackets2(input, idx, size) == IF idx > Len(input) \/ size = 0
                                 THEN <<>>
                                 ELSE << <<idx, input[idx]>> >> \o getPackets2(input, idx+1, size-1)


vars == << slidingIdx, outputWire, inputWire, state, pc >>

ProcSet == {"SynAck"} \cup {"SendSynAck"} \cup {"ReceiveButFirst"} \cup {"Sender"} \cup {"ACK"}

Init == (* Global variables *)
        /\ slidingIdx = 1
        /\ outputWire = <<>>
        /\ inputWire = <<>>
        /\ state = "WAITING"
        /\ pc = [self \in ProcSet |-> CASE self = "SynAck" -> "A_"
                                        [] self = "SendSynAck" -> "A_S"
                                        [] self = "ReceiveButFirst" -> "A_R"
                                        [] self = "Sender" -> "A_s"
                                        [] self = "ACK" -> "A"]

A_ == /\ pc["SynAck"] = "A_"
      /\ IF state = "WAITING"
            THEN /\ inputWire # <<>>
                 /\ IF inputWire[1] # Corruption
                       THEN /\ state' = "OPENING"
                       ELSE /\ TRUE
                            /\ state' = state
                 /\ inputWire' = <<>>
                 /\ pc' = [pc EXCEPT !["SynAck"] = "A_"]
            ELSE /\ pc' = [pc EXCEPT !["SynAck"] = "Done"]
                 /\ UNCHANGED << inputWire, state >>
      /\ UNCHANGED << slidingIdx, outputWire >>

ReceiveSyn == A_

A_S == /\ pc["SendSynAck"] = "A_S"
       /\ state = "OPENING" /\ outputWire = <<>>
       /\ outputWire' = <<<<0, "SYNACK">>>>
       /\ pc' = [pc EXCEPT !["SendSynAck"] = "A_S"]
       /\ UNCHANGED << slidingIdx, inputWire, state >>

SendSynAck == A_S

A_R == /\ pc["ReceiveButFirst"] = "A_R"
       /\ state = "OPENING" /\ inputWire # <<>>
       /\ IF Head(inputWire) # Corruption /\ Head(inputWire)[1] = "ACK" /\ Head(inputWire)[2] = slidingIdx
             THEN /\ state' = "OPEN"
             ELSE /\ PrintT((inputWire))
                  /\ state' = state
       /\ inputWire' = Tail(inputWire)
       /\ pc' = [pc EXCEPT !["ReceiveButFirst"] = "A_R"]
       /\ UNCHANGED << slidingIdx, outputWire >>

ReceiveFirstAck == A_R

A_s == /\ pc["Sender"] = "A_s"
       /\ /\ outputWire = <<>>
          /\ slidingIdx <= Len(MESSAGE)
          /\ state = "OPEN"
       /\ outputWire' = getPackets(MESSAGE, slidingIdx)
       /\ pc' = [pc EXCEPT !["Sender"] = "A_s"]
       /\ UNCHANGED << slidingIdx, inputWire, state >>

sendWindow == A_s

A == /\ pc["ACK"] = "A"
     /\ /\ inputWire # <<>>
        /\ state = "OPEN"
     /\ IF Head(inputWire) # Corruption /\ Head(inputWire)[2] >= slidingIdx
           THEN /\ slidingIdx' = Head(inputWire)[2] + 1
           ELSE /\ TRUE
                /\ UNCHANGED slidingIdx
     /\ inputWire' = Tail(inputWire)
     /\ pc' = [pc EXCEPT !["ACK"] = "A"]
     /\ UNCHANGED << outputWire, state >>

receiveLatest == A

Next == ReceiveSyn \/ SendSynAck \/ ReceiveFirstAck \/ sendWindow
           \/ receiveLatest

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ReceiveSyn)
        /\ WF_vars(SendSynAck)
        /\ WF_vars(ReceiveFirstAck)
        /\ WF_vars(sendWindow)
        /\ WF_vars(receiveLatest)

\* END TRANSLATION

Fairness == /\ WF_vars(ReceiveSyn)
            /\ WF_vars(SendSynAck)
            /\ WF_vars(ReceiveFirstAck)
            /\ WF_vars(sendWindow)
            /\ WF_vars(receiveLatest)
\*            /\ WF_vars(timeOut_)
=============================================================================
\* Modification History
\* Last modified Mon Jun 17 00:10:39 NZST 2019 by jb567
\* Created Sat Jun 01 15:31:37 NZST 2019 by jb567
