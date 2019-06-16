---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156072240345279000 == 
<<1,2,3,4,5,6,7,8,9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156072240345280000 == 
3
----

\* NEXT definition @modelBehaviorNext:0
next_156072240345381000 ==
multiplace!Next /\ UNCHANGED <<dataWireIn, dataWireOut, ackWireIn, 
			ackWireOut, senderPc, ackSeqNum, receiverState, senderState>>
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 10:00:03 NZST 2019 by jb567
