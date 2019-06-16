---------------------------- MODULE gbnReceiver ----------------------------
EXTENDS Sequences, Naturals, TLC

CONSTANT CORRUPT_DATA

(*--algorithm GoBackNReceiver
variables
    output = <<>>,
    outputWire = <<>>,
    ackSeqNum = 0,
    state = "WAITING",
    inputWire = <<>>;

define
    RECURSIVE DropCorrupt(_)
    DropCorrupt(packets) == IF packets = <<>> THEN <<>>
                            ELSE IF Head(packets) = CORRUPT_DATA THEN DropCorrupt(Tail(packets))
                            ELSE <<Head(packets)>> \o DropCorrupt(Tail(packets))
\*    SeqMap(Op(_), seq) == [x \in DOMAIN seq |-> Op(seq[x])]
    RECURSIVE SeqMap(_,_)
    
    SeqMap(op(_), seq) == IF Len(seq) = 0 THEN <<>>
                          ELSE <<op(Head(seq))>> \o SeqMap(op, Tail(seq))
    
    Second(item) == item[2]
    RECURSIVE TakeN(_,_)
    TakeN(items,acceptedIdx) == IF Len(items) = 0 THEN 0
                                ELSE IF Head(items)[1] = acceptedIdx + 1 THEN 1 + TakeN(Tail(items), acceptedIdx + 1)
                                ELSE 0
end define;

fair process SYN = "SYN"
begin A:
while TRUE do
    await /\ state = "WAITING"
          /\ outputWire = <<>>;
    outputWire := <<<<"SYN", ackSeqNum>>>>
end while;
end process;

fair process FirstAck = "ACK"
begin A:
while TRUE do
    await /\ state = "WAITING"
          /\ inputWire # <<>>;
    if Head(inputWire) # CORRUPT_DATA /\ Head(inputWire)[2] = "SYNACK" then
        state := "OPEN";
    end if;
    inputWire := <<>>;
end while;
end process;

fair process receiver = "GBN Receiver"
begin A:
while TRUE do
    await /\ inputWire # <<>>
          /\ state = "OPEN";
    output := output \o 
        SeqMap(
            Second,
            SubSeq(DropCorrupt(inputWire), 1, 
                TakeN(DropCorrupt(inputWire), ackSeqNum))
        );
    ackSeqNum := ackSeqNum + TakeN(DropCorrupt(inputWire), ackSeqNum);
    inputWire := <<>>;
end while;
end process;

fair process sender = "GBN Receiver ACK"
begin A:
while TRUE do
    await /\ outputWire = <<>>
          /\ state = "OPEN";
    outputWire := << <<"ACK", ackSeqNum>> >>;
end while;
end process;


end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process SYN at line 34 col 1 changed to A_
\* Label A of process FirstAck at line 43 col 1 changed to A_F
\* Label A of process receiver at line 55 col 1 changed to A_r
VARIABLES output, outputWire, ackSeqNum, state, inputWire

(* define statement *)
RECURSIVE DropCorrupt(_)
DropCorrupt(packets) == IF packets = <<>> THEN <<>>
                        ELSE IF Head(packets) = CORRUPT_DATA THEN DropCorrupt(Tail(packets))
                        ELSE <<Head(packets)>> \o DropCorrupt(Tail(packets))

RECURSIVE SeqMap(_,_)

SeqMap(op(_), seq) == IF Len(seq) = 0 THEN <<>>
                      ELSE <<op(Head(seq))>> \o SeqMap(op, Tail(seq))

Second(item) == item[2]
RECURSIVE TakeN(_,_)
TakeN(items,acceptedIdx) == IF Len(items) = 0 THEN 0
                            ELSE IF Head(items)[1] = acceptedIdx + 1 THEN 1 + TakeN(Tail(items), acceptedIdx + 1)
                            ELSE 0


vars == << output, outputWire, ackSeqNum, state, inputWire >>

ProcSet == {"SYN"} \cup {"ACK"} \cup {"GBN Receiver"} \cup {"GBN Receiver ACK"}

Init == (* Global variables *)
        /\ output = <<>>
        /\ outputWire = <<>>
        /\ ackSeqNum = 0
        /\ state = "WAITING"
        /\ inputWire = <<>>

SYN == /\ /\ state = "WAITING"
          /\ outputWire = <<>>
       /\ outputWire' = <<<<"SYN", ackSeqNum>>>>
       /\ UNCHANGED << output, ackSeqNum, state, inputWire >>

FirstAck == /\ /\ state = "WAITING"
               /\ inputWire # <<>>
            /\ IF Head(inputWire) # CORRUPT_DATA /\ Head(inputWire)[2] = "SYNACK"
                  THEN /\ state' = "OPEN"
                  ELSE /\ TRUE
                       /\ state' = state
            /\ inputWire' = <<>>
            /\ UNCHANGED << output, outputWire, ackSeqNum >>

receiver == /\ /\ inputWire # <<>>
               /\ state = "OPEN"
            /\ output' =       output \o
                         SeqMap(
                             Second,
                             SubSeq(DropCorrupt(inputWire), 1,
                                 TakeN(DropCorrupt(inputWire), ackSeqNum))
                         )
            /\ ackSeqNum' = ackSeqNum + TakeN(DropCorrupt(inputWire), ackSeqNum)
            /\ inputWire' = <<>>
            /\ UNCHANGED << outputWire, state >>

sender == /\ /\ outputWire = <<>>
             /\ state = "OPEN"
          /\ outputWire' = << <<"ACK", ackSeqNum>> >>
          /\ UNCHANGED << output, ackSeqNum, state, inputWire >>

Next == SYN \/ FirstAck \/ receiver \/ sender

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(SYN)
        /\ WF_vars(FirstAck)
        /\ WF_vars(receiver)
        /\ WF_vars(sender)

\* END TRANSLATION
Fairness == /\ WF_vars(receiver)
            /\ WF_vars(sender)
            /\ WF_vars(SYN)
            /\ WF_vars(FirstAck)
            

=============================================================================
\* Modification History
\* Last modified Mon Jun 17 00:06:33 NZST 2019 by jb567
\* Created Mon Jun 03 09:20:20 NZST 2019 by jb567
