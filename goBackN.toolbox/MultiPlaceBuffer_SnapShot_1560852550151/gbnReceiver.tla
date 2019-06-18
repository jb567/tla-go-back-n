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
    \* This will strip all corrupt packets out, as corrupt packets break the TakeWhile operation
    RECURSIVE DropCorrupt(_)
    DropCorrupt(packets) == IF packets = <<>> THEN <<>>
                            ELSE IF Head(packets) = CORRUPT_DATA THEN DropCorrupt(Tail(packets))
                            ELSE <<Head(packets)>> \o DropCorrupt(Tail(packets))

    \* A simple Map operator for sequences
    RECURSIVE SeqMap(_,_)
    \*    SeqMap(Op(_), seq) == [x \in DOMAIN seq |-> Op(seq[x])]
    SeqMap(op(_), seq) == IF Len(seq) = 0 THEN <<>>
                          ELSE <<op(Head(seq))>> \o SeqMap(op, Tail(seq))

    \* A function to take the second item from a sequence (used with seq map to extract packet data)
    Second(item) == item[2]

    \* Will return the longest subsequence of correct/acceptable packets
    RECURSIVE TakeWhile(_,_)
    TakeWhile(items,acceptedIdx) == IF Len(items) = 0 THEN 0
                                ELSE IF Head(items)[1] = acceptedIdx + 1 THEN 1 + TakeWhile(Tail(items), acceptedIdx + 1)
                                ELSE 0
end define;

\* ===================
\* TCP HANDSHAKE START
\* ===================

\* This represents the first stage of opening a connection, the request for a connection to be formed
\* This simply repeats a message constantly until a connection is established
fair process SYN = "SYN"
begin A:
while TRUE do
    await /\ state = "WAITING"
          /\ outputWire = <<>>;
    outputWire := <<<<"SYN", ackSeqNum>>>>
end while;
end process;

\* This is the receiver for the TCP Handshake
\* Because of the way the 3 way handshake works after this second element is received, the 
\* last message is a "normal" ACK, this special ACK exists to make sure the SYNACK is
\* not considered part of the normal message
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

\* =================
\* TCP HANDSHAKE END
\* =================

\* ====================
\* SLIDING WINDOW START
\* ====================

\* Receives messages from the input
\* Gets all the messages from the start that are valid 
\* until one is not, then gets the message and appends
\* this to the output
fair process receiver = "GBN Receiver"
begin A:
while TRUE do
    await /\ inputWire # <<>>
          /\ state = "OPEN";
    output := output \o 
        \* Map the valid packet list -> output
        SeqMap(
            Second,
            \* Generate the subsequence of valid items
            SubSeq(DropCorrupt(inputWire), 1, 
                TakeWhile(DropCorrupt(inputWire), ackSeqNum))
        );
    ackSeqNum := ackSeqNum + TakeWhile(DropCorrupt(inputWire), ackSeqNum);
    \* Clear the input
    inputWire := <<>>;
end while;
end process;

\* Sends acknowledgements one at a time
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
\* Label A of process SYN at line 45 col 1 changed to A_
\* Label A of process FirstAck at line 58 col 1 changed to A_F
\* Label A of process receiver at line 78 col 1 changed to A_r
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


RECURSIVE TakeWhile(_,_)
TakeWhile(items,acceptedIdx) == IF Len(items) = 0 THEN 0
                            ELSE IF Head(items)[1] = acceptedIdx + 1 THEN 1 + TakeWhile(Tail(items), acceptedIdx + 1)
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
                                 TakeWhile(DropCorrupt(inputWire), ackSeqNum))
                         )
            /\ ackSeqNum' = ackSeqNum + TakeWhile(DropCorrupt(inputWire), ackSeqNum)
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
\* Last modified Mon Jun 17 10:24:33 NZST 2019 by jb567
\* Created Mon Jun 03 09:20:20 NZST 2019 by jb567
