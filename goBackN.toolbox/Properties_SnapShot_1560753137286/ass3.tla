-------------------------------- MODULE ass3 --------------------------------
EXTENDS TLC, Sequences, Naturals
CONSTANTS MESSAGE, WINDOW_SIZE, CORRUPT_DATA

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

\* Ghost variables
VARIABLES buffer, n

vars == <<dataWireIn, dataWireOut, ackWireIn, ackWireOut, senderIdx, senderPc, output, ackSeqNum, senderState, receiverState, buffer, n>>

sender == INSTANCE slidingSender WITH inputWire <- ackWireOut , outputWire <- dataWireIn, state <- senderState,
            slidingIdx <- senderIdx, pc <- senderPc

dataWire == INSTANCE dataWire WITH input <- dataWireIn, output <- dataWireOut
ackWire == INSTANCE dataWire WITH input <- ackWireIn, output <- ackWireOut

receiver == INSTANCE gbnReceiver WITH inputWire <- dataWireOut, outputWire <- ackWireIn, state <- receiverState

multiplace == INSTANCE mpb WITH index <- senderIdx
Tcp == INSTANCE tcp

Init == /\ sender!Init
        /\ receiver!Init
        /\ dataWire!Init
        /\ ackWire!Init
        /\ multiplace!Init

Next == /\ \/ sender!Next /\ UNCHANGED <<dataWireOut, ackWireIn, output, ackSeqNum, receiverState>>
           \/ dataWire!Next /\ UNCHANGED <<ackWireIn, ackWireOut, output, ackSeqNum, senderIdx, senderState, senderPc, receiverState>>
           \/ ackWire!Next /\ UNCHANGED <<dataWireIn, dataWireOut, output, ackSeqNum, senderIdx, senderState, senderPc, receiverState>>
           \/ receiver!Next /\ UNCHANGED <<dataWireIn, ackWireOut, senderIdx, senderState, senderPc>>
        /\ UNCHANGED <<buffer, n>>


Fairness == /\ sender!Fairness
            /\ dataWire!Fairness
            /\ ackWire!Fairness
            /\ receiver!Fairness
            /\ SF_vars(/\ dataWire!Next
                       /\ \A x \in 1..Len(dataWireOut'): dataWireOut'[x][1] = ackSeqNum+x)
  
Spec == /\ Init
        /\ [][Next]_vars
        /\ Fairness

              \* In the future the message will eventually be received, and it will not be corrupted
Properties == /\ <>[](output = MESSAGE)
              \* The output received will always be a partially completed message
              /\ [](output = <<>> \/ \E x \in (1..(Len(MESSAGE))): output = SubSeq(MESSAGE,1,x))
              \*/\ [](output # MESSAGE => dataWire!Next ~> sender!Next)
              \*/\ [](LET x == Len(output) IN output # MESSAGE ~> (Len(output) >= x))

=============================================================================
\* Modification History
\* Last modified Mon Jun 17 18:32:12 NZST 2019 by jb567
\* Created Sat Jun 01 15:31:20 NZST 2019 by jb567
