---- MODULE MC ----
EXTENDS ass3, TLC

\* NEXT definition @modelBehaviorNext:0
next_156072208168557000 ==
Tcp!Next /\ UNCHANGED <<dataWireIn, dataWireOut, ackWireIn, ackWireOut, senderIdx, senderPc, output, ackSeqNum, buffer, n>>
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 09:54:41 NZST 2019 by jb567
