---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156068727790365000 == 
<<"HELLO", "WORLD", "SANJAY", "SAYS", "YOURE", "SILLY">>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156068727790366000 == 
2
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_156068727790368000 ==
[](output # MESSAGE)
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 00:14:37 NZST 2019 by jb567
