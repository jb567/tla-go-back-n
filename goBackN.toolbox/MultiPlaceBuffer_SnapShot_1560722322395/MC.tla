---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156072232037361000 == 
<<1,2,3,4,5,6,7,8,9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156072232037362000 == 
3
----

\* NEXT definition @modelBehaviorNext:0
next_156072232037463000 ==
multiplace!Next /\ UNCHANGED <<dataWireIn, dataWireOut, ackWireIn, 
			ackWireOut, senderPc, ackSeqNum, buffer, n>>
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 09:58:40 NZST 2019 by jb567
