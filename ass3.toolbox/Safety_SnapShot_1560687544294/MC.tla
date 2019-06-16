---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156068754226087000 == 
<<"HELLO", "WORLD", "SANJAY", "SAYS", "YOURE", "SILLY">>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156068754226088000 == 
2
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_156068754226190000 ==
multiplace!Spec
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 00:19:02 NZST 2019 by jb567
