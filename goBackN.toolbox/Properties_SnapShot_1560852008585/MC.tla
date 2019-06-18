---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156085200356310000 == 
<< 1, 2, 3, 4, 5, 6, 7, 8, 9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156085200356311000 == 
3
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_156085200356313000 ==
Tcp!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jun 18 22:00:03 NZST 2019 by jb567
