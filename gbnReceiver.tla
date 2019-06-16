---------------------------- MODULE gbnReceiver ----------------------------
EXTENDS Sequences, Naturals, TLC

CONSTANT Corruption

(*--algorithm GoBackNReceiver
variables
    output = <<>>,
    outputWire = <<>>,
    ackSeqNum = 0,
    
    inputWire = <<>>;

define
    RECURSIVE DropCorrupt(_)
    DropCorrupt(packets) == IF packets = <<>> THEN <<>>
                            ELSE IF Head(packets) = Corruption THEN DropCorrupt(Tail(packets))
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

\*fair+ process SYN = "SYN"
\*begin A:
\*while TRUE do
\*    await /\ inputWire # <<>>;
\*    outputWire :=  
\*end while;
\*end process;

fair process receiver = "GBN Receiver"
begin A:
while TRUE do
    await /\ inputWire # <<>>;
    print(DropCorrupt(inputWire));
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
    await /\ outputWire = <<>>;
    outputWire := <<ackSeqNum>>;
end while;
end process;


end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process receiver at line 42 col 1 changed to A_
VARIABLES output, outputWire, ackSeqNum, inputWire

(* define statement *)
RECURSIVE DropCorrupt(_)
DropCorrupt(packets) == IF packets = <<>> THEN <<>>
                        ELSE IF Head(packets) = Corruption THEN DropCorrupt(Tail(packets))
                        ELSE <<Head(packets)>> \o DropCorrupt(Tail(packets))

RECURSIVE SeqMap(_,_)

SeqMap(op(_), seq) == IF Len(seq) = 0 THEN <<>>
                      ELSE <<op(Head(seq))>> \o SeqMap(op, Tail(seq))

Second(item) == item[2]
RECURSIVE TakeN(_,_)
TakeN(items,acceptedIdx) == IF Len(items) = 0 THEN 0
                            ELSE IF Head(items)[1] = acceptedIdx + 1 THEN 1 + TakeN(Tail(items), acceptedIdx + 1)
                            ELSE 0


vars == << output, outputWire, ackSeqNum, inputWire >>

ProcSet == {"GBN Receiver"} \cup {"GBN Receiver ACK"}

Init == (* Global variables *)
        /\ output = <<>>
        /\ outputWire = <<>>
        /\ ackSeqNum = 0
        /\ inputWire = <<>>

receiver == /\ /\ inputWire # <<>>
            /\ PrintT((DropCorrupt(inputWire)))
            /\ output' =       output \o
                         SeqMap(
                             Second,
                             SubSeq(DropCorrupt(inputWire), 1,
                                 TakeN(DropCorrupt(inputWire), ackSeqNum))
                         )
            /\ ackSeqNum' = ackSeqNum + TakeN(DropCorrupt(inputWire), ackSeqNum)
            /\ inputWire' = <<>>
            /\ UNCHANGED outputWire

sender == /\ /\ outputWire = <<>>
          /\ outputWire' = <<ackSeqNum>>
          /\ UNCHANGED << output, ackSeqNum, inputWire >>

Next == receiver \/ sender

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(receiver)
        /\ WF_vars(sender)

\* END TRANSLATION
Fairness == /\ WF_vars(receiver)
            /\ WF_vars(sender)

=============================================================================
\* Modification History
\* Last modified Mon Jun 03 12:31:58 NZST 2019 by jb567
\* Created Mon Jun 03 09:20:20 NZST 2019 by jb567
