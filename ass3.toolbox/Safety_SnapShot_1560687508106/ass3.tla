-------------------------------- MODULE ass3 --------------------------------
EXTENDS TLC, Sequences, Naturals
CONSTANTS MESSAGE, WINDOW_SIZE, Corruption

VARIABLES
    dataWireIn,
    dataWireOut,
    ackWireIn,
    ackWireOut,
    senderIdx,
    senderPc,
    output,
    senderState,
    ackSeqNum,
    receiverState

vars == <<dataWireIn, dataWireOut, ackWireIn, ackWireOut, senderIdx, senderPc, output, ackSeqNum, senderState, receiverState>>


sender == INSTANCE slidingSender WITH inputWire <- ackWireOut , outputWire <- dataWireIn, state <- senderState,
            slidingIdx <- senderIdx, pc <- senderPc

dataWire == INSTANCE dataWire WITH input <- dataWireIn, output <- dataWireOut
ackWire == INSTANCE dataWire WITH input <- ackWireIn, output <- ackWireOut

receiver == INSTANCE gbnReceiver WITH inputWire <- dataWireOut, outputWire <- ackWireIn, state <- receiverState

VARIABLES buffer, n
multiplace == INSTANCE mpb WITH index <- senderIdx


Init == /\ sender!Init
        /\ receiver!Init
        /\ dataWire!Init
        /\ ackWire!Init

Next == /\ \/ sender!Next /\ UNCHANGED <<dataWireOut, ackWireIn, output, ackSeqNum, receiverState>>
           \/ dataWire!Next /\ UNCHANGED <<ackWireIn, ackWireOut, output, ackSeqNum, senderIdx, senderState, senderPc, receiverState>>
           \/ ackWire!Next /\ UNCHANGED <<dataWireIn, dataWireOut, output, ackSeqNum, senderIdx, senderState, senderPc, receiverState>>
           \/ receiver!Next /\ UNCHANGED <<dataWireIn, ackWireOut, senderIdx, senderState, senderPc>>
        /\ UNCHANGED <<buffer, n>>


Fairness == /\ sender!Fairness
            /\ dataWire!Fairness
            /\ ackWire!Fairness
            /\ receiver!Fairness
  
Spec == /\ Init
        /\ [][Next]_vars
        /\ Fairness
      
Properties == /\ <>[](output = MESSAGE)
              /\ [](output = <<>> \/ \E x \in (1..(Len(MESSAGE))): output = SubSeq(MESSAGE,1,x))
              \*/\ [](LET x == Len(output) IN output # MESSAGE ~> (Len(output) >= x))
=============================================================================
\* Modification History
\* Last modified Mon Jun 17 00:18:22 NZST 2019 by jb567
\* Created Sat Jun 01 15:31:20 NZST 2019 by jb567
