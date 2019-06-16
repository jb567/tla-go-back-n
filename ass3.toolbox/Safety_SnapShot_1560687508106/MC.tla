---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156068750607883000 == 
<<"HELLO", "WORLD", "SANJAY", "SAYS", "YOURE", "SILLY">>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156068750607884000 == 
2
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_156068750607886000 ==
multiplace!Spec
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 00:18:26 NZST 2019 by jb567
