--------------------------- MODULE slidingSender ---------------------------
EXTENDS Naturals, Sequences
CONSTANTS MESSAGE, WINDOW_SIZE, Corruption
ASSUME WINDOW_SIZE \in 0..99

VARIABLE pc

(*--algorithm SlidingSender
variables
    slidingIdx = 1,
    outputWire = <<>>,
    inputWire = <<>>,
    timeOut = FALSE;
define

RECURSIVE getPackets2(_,_,_)

getPackets(input,idx) == getPackets2(input, idx, WINDOW_SIZE)

getPackets2(input, idx, size) == IF idx > Len(input) \/ size = 0
                                 THEN <<>>
                                 ELSE << <<idx, input[idx]>> >> \o getPackets2(input, idx+1, size-1)

end define
fair process sendWindow = "Sender"
begin A:
while TRUE do
    \*toSend
    await /\ outputWire = <<>>
          /\ slidingIdx <= Len(MESSAGE)
          /\ ~timeOut;
    outputWire := getPackets(MESSAGE, slidingIdx);
end while;
end process;

fair process receiveLatest = "ACK"
begin A:
while TRUE do
    await /\ inputWire # <<>>
          /\ ~timeOut;
    if inputWire # <<Corruption>> /\ inputWire[1] >= slidingIdx then
        slidingIdx := inputWire[1] + 1;
    end if;
    inputWire := <<>>;
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
\* Label A of process sendWindow at line 27 col 1 changed to A_
VARIABLES slidingIdx, outputWire, inputWire, timeOut

(* define statement *)
RECURSIVE getPackets2(_,_,_)

getPackets(input,idx) == getPackets2(input, idx, WINDOW_SIZE)

getPackets2(input, idx, size) == IF idx > Len(input) \/ size = 0
                                 THEN <<>>
                                 ELSE << <<idx, input[idx]>> >> \o getPackets2(input, idx+1, size-1)


vars == << slidingIdx, outputWire, inputWire, timeOut >>

ProcSet == {"Sender"} \cup {"ACK"}

Init == (* Global variables *)
        /\ slidingIdx = 1
        /\ outputWire = <<>>
        /\ inputWire = <<>>
        /\ timeOut = FALSE
        /\ pc = <<>>

sendWindow == /\ /\ outputWire = <<>>
                 /\ slidingIdx <= Len(MESSAGE)
                 /\ ~timeOut
              /\ outputWire' = getPackets(MESSAGE, slidingIdx)
              /\ UNCHANGED << slidingIdx, inputWire, timeOut >>

receiveLatest == /\ /\ inputWire # <<>>
                    /\ ~timeOut
                 /\ IF inputWire # <<Corruption>> /\ inputWire[1] >= slidingIdx
                       THEN /\ slidingIdx' = inputWire[1] + 1
                       ELSE /\ TRUE
                            /\ UNCHANGED slidingIdx
                 /\ inputWire' = <<>>
                 /\ UNCHANGED << outputWire, timeOut >>

Next == sendWindow \/ receiveLatest

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(sendWindow)
        /\ WF_vars(receiveLatest)

\* END TRANSLATION

Fairness == /\ WF_vars(sendWindow)
            /\ WF_vars(receiveLatest)
\*            /\ WF_vars(timeOut_)
=============================================================================
\* Modification History
\* Last modified Mon Jun 03 11:04:17 NZST 2019 by jb567
\* Created Sat Jun 01 15:31:37 NZST 2019 by jb567
