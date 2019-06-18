--------------------------- MODULE slidingSender ---------------------------
EXTENDS Naturals, Sequences, TLC, Util
CONSTANTS MESSAGE, CORRUPT_DATA
ASSUME WINDOW_SIZE \in 0..99


(*--algorithm SlidingSender
variables
    slidingIdx = 1,
    outputWire = <<>>,
    inputWire = <<>>,
    startNum \in 1..5,
    state = "WAITING";

(* =====================
   3 WAY HANDSHAKE START
   ===================== *)

(* Passive Open Awaiting connection request
   - Only should be called once
   - Upon receiving a valid SYN packet open the connection, which allows for data to be sent
*)
fair process ReceiveSyn = "SynAck"
begin A:
while state = "WAITING" do
    await inputWire # <<>>;
    if inputWire[1] # CORRUPT_DATA /\ Head(inputWire)[1] = "SYN" then
        state := "OPENING";
        \*otherStart := Head(inputWire)[2];
    end if;
    inputWire := Tail(inputWire);
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
    if Head(inputWire) # CORRUPT_DATA /\ Head(inputWire)[1] = "ACK" /\ Head(inputWire)[2] = slidingIdx-1 then
        state := "OPEN";
    end if;
    inputWire := Tail(inputWire);
end while;
end process;

(* ===================
   3 WAY HANDSHAKE END
   =================== *)

(* ====================
   SLIDING WINDOW START
   ==================== *)


fair process sendWindow = "Sender"
begin A:
while TRUE do
    \*toSend
    await /\ outputWire = <<>>
          /\ slidingIdx <= Len(MESSAGE)
          /\ state = "OPEN";
    outputWire := getPackets(MESSAGE, 0, slidingIdx);
end while;
end process;

fair process receiveLatest = "ACK"
begin A:
while TRUE do
    await /\ inputWire # <<>>
          /\ state = "OPEN";
    if Head(inputWire) # CORRUPT_DATA /\ InWindow(slidingIdx, 0, Head(inputWire)[2]) then
        slidingIdx := slidingIdx + WindowPos(ConvertIdx(0,slidingIdx), Head(inputWire)[2]);
    end if;
    inputWire := Tail(inputWire);
end while;
end process;

(* ==================
   SLIDING WINDOW END
   ================== *)

end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process ReceiveSyn at line 25 col 1 changed to A_
\* Label A of process SendSynAck at line 37 col 1 changed to A_S
\* Label A of process ReceiveFirstAck at line 45 col 1 changed to A_R
\* Label A of process sendWindow at line 65 col 1 changed to A_s
VARIABLES slidingIdx, outputWire, inputWire, startNum, state, pc

vars == << slidingIdx, outputWire, inputWire, startNum, state, pc >>

ProcSet == {"SynAck"} \cup {"SendSynAck"} \cup {"ReceiveButFirst"} \cup {"Sender"} \cup {"ACK"}

Init == (* Global variables *)
        /\ slidingIdx = 1
        /\ outputWire = <<>>
        /\ inputWire = <<>>
        /\ startNum \in 1..5
        /\ state = "WAITING"
        /\ pc = [self \in ProcSet |-> CASE self = "SynAck" -> "A_"
                                        [] self = "SendSynAck" -> "A_S"
                                        [] self = "ReceiveButFirst" -> "A_R"
                                        [] self = "Sender" -> "A_s"
                                        [] self = "ACK" -> "A"]

A_ == /\ pc["SynAck"] = "A_"
      /\ IF state = "WAITING"
            THEN /\ inputWire # <<>>
                 /\ IF inputWire[1] # CORRUPT_DATA /\ Head(inputWire)[1] = "SYN"
                       THEN /\ state' = "OPENING"
                       ELSE /\ TRUE
                            /\ state' = state
                 /\ inputWire' = Tail(inputWire)
                 /\ pc' = [pc EXCEPT !["SynAck"] = "A_"]
            ELSE /\ pc' = [pc EXCEPT !["SynAck"] = "Done"]
                 /\ UNCHANGED << inputWire, state >>
      /\ UNCHANGED << slidingIdx, outputWire, startNum >>

ReceiveSyn == A_

A_S == /\ pc["SendSynAck"] = "A_S"
       /\ state = "OPENING" /\ outputWire = <<>>
       /\ outputWire' = <<<<0, "SYNACK">>>>
       /\ pc' = [pc EXCEPT !["SendSynAck"] = "A_S"]
       /\ UNCHANGED << slidingIdx, inputWire, startNum, state >>

SendSynAck == A_S

A_R == /\ pc["ReceiveButFirst"] = "A_R"
       /\ state = "OPENING" /\ inputWire # <<>>
       /\ IF Head(inputWire) # CORRUPT_DATA /\ Head(inputWire)[1] = "ACK" /\ Head(inputWire)[2] = slidingIdx-1
             THEN /\ state' = "OPEN"
             ELSE /\ TRUE
                  /\ state' = state
       /\ inputWire' = Tail(inputWire)
       /\ pc' = [pc EXCEPT !["ReceiveButFirst"] = "A_R"]
       /\ UNCHANGED << slidingIdx, outputWire, startNum >>

ReceiveFirstAck == A_R

A_s == /\ pc["Sender"] = "A_s"
       /\ /\ outputWire = <<>>
          /\ slidingIdx <= Len(MESSAGE)
          /\ state = "OPEN"
       /\ outputWire' = getPackets(MESSAGE, 0, slidingIdx)
       /\ pc' = [pc EXCEPT !["Sender"] = "A_s"]
       /\ UNCHANGED << slidingIdx, inputWire, startNum, state >>

sendWindow == A_s

A == /\ pc["ACK"] = "A"
     /\ /\ inputWire # <<>>
        /\ state = "OPEN"
     /\ IF Head(inputWire) # CORRUPT_DATA /\ InWindow(slidingIdx, 0, Head(inputWire)[2])
           THEN /\ slidingIdx' = slidingIdx + WindowPos(ConvertIdx(0,slidingIdx), Head(inputWire)[2])
           ELSE /\ TRUE
                /\ UNCHANGED slidingIdx
     /\ inputWire' = Tail(inputWire)
     /\ pc' = [pc EXCEPT !["ACK"] = "A"]
     /\ UNCHANGED << outputWire, startNum, state >>

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
\* Last modified Tue Jun 18 21:57:18 NZST 2019 by jb567
\* Created Sat Jun 01 15:31:37 NZST 2019 by jb567
