---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156068745466479000 == 
<<"HELLO", "WORLD", "SANJAY", "SAYS", "YOURE", "SILLY">>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156068745466480000 == 
2
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_156068745466482000 ==
multiplace!Spec
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 00:17:34 NZST 2019 by jb567
