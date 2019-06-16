---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156072235670770000 == 
<<1,2,3,4,5,6,7,8,9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156072235670771000 == 
3
----

\* NEXT definition @modelBehaviorNext:0
next_156072235670872000 ==
multiplace!Next /\ UNCHANGED <<dataWireIn, dataWireOut, ackWireIn, 
			ackWireOut, senderPc>>
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 09:59:16 NZST 2019 by jb567
