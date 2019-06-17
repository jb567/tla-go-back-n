---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156076613750358000 == 
<<1,2,3,4,5,6,7,8,9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156076613750359000 == 
3
----

\* NEXT definition @modelBehaviorNext:0
next_156076613750360000 ==
multiplace!Next /\ UNCHANGED <<dataWireIn, dataWireOut, ackWireIn, 
			ackWireOut, senderPc, ackSeqNum, receiverState, senderState>>
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 22:08:57 NZST 2019 by jb567
