-------------------------------- MODULE ass3 --------------------------------
EXTENDS TLC, Sequences, Naturals
CONSTANTS MESSAGE, WINDOW_SIZE, Corruption

VARIABLES
    dataWireIn,
    dataWireOut,
    ackWireIn,
    ackWireOut,
    senderIdx,
    senderTimeOut,
    senderPc,
    output,
    ackSeqNum

vars == <<dataWireIn, dataWireOut, ackWireIn, ackWireOut, senderIdx, senderTimeOut, senderPc, output, ackSeqNum>>


sender == INSTANCE slidingSender WITH inputWire <- ackWireOut , outputWire <- dataWireIn, timeOut <- senderTimeOut,
            slidingIdx <- senderIdx, pc <- senderPc

dataWire == INSTANCE dataWire WITH input <- dataWireIn, output <- dataWireOut
ackWire == INSTANCE dataWire WITH input <- ackWireIn, output <- ackWireOut

receiver == INSTANCE gbnReceiver WITH inputWire <- dataWireOut, outputWire <- ackWireIn

Init == /\ sender!Init
        /\ receiver!Init
        /\ dataWire!Init
        /\ ackWire!Init

Next == \/ sender!Next /\ UNCHANGED <<senderPc, dataWireOut, ackWireIn, output, ackSeqNum>>
        \/ dataWire!Next /\ UNCHANGED <<ackWireIn, ackWireOut, output, ackSeqNum, senderIdx, senderTimeOut, senderPc>>
        \/ ackWire!Next /\ UNCHANGED <<dataWireIn, dataWireOut, output, ackSeqNum, senderIdx, senderTimeOut, senderPc>>
        \/ receiver!Next /\ UNCHANGED <<dataWireIn, ackWireOut, senderIdx, senderTimeOut, senderPc>>


Fairness == /\ sender!Fairness
            /\ dataWire!Fairness
            /\ ackWire!Fairness
            /\ receiver!Fairness
  
Spec == /\ Init
        /\ [][Next]_vars
        /\ Fairness
      
Properties == /\ <>[](output = MESSAGE)
              /\ [](output = <<>> \/ \E x \in (1..(Len(MESSAGE))): output = SubSeq(MESSAGE,1,x))
              /\ [](LET x == Len(output) IN output # MESSAGE ~> (Len(output) >= x))
=============================================================================
\* Modification History
\* Last modified Mon Jun 03 12:02:29 NZST 2019 by jb567
\* Created Sat Jun 01 15:31:20 NZST 2019 by jb567
