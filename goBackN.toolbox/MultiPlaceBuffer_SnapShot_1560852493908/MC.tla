---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156085249188014000 == 
<<1,2,3,4,5,6,7,8,9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156085249188015000 == 
3
----

\* NEXT definition @modelBehaviorNext:0
next_156085249188116000 ==
multiplace!Next /\ UNCHANGED <<dataWireIn, dataWireOut, ackWireIn, 
			ackWireOut, senderPc, ackSeqNum, receiverState, senderState>>
----
=============================================================================
\* Modification History
\* Created Tue Jun 18 22:08:11 NZST 2019 by jb567
