---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156085254811917000 == 
<<1,2,3,4,5,6,7,8,9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156085254811918000 == 
3
----

\* NEXT definition @modelBehaviorNext:0
next_156085254812019000 ==
multiplace!Next /\ UNCHANGED <<dataWireIn, dataWireOut, ackWireIn, 
			ackWireOut, senderPc, ackSeqNum, receiverState, senderState>>
----
=============================================================================
\* Modification History
\* Created Tue Jun 18 22:09:08 NZST 2019 by jb567
