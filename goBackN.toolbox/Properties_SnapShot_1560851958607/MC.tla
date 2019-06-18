---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_15608519525656000 == 
<< 1, 2, 3, 4, 5, 6, 7, 8, 9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_15608519525657000 == 
3
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_15608519525659000 ==
Tcp!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jun 18 21:59:12 NZST 2019 by jb567
