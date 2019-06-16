---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_15606902097716000 == 
<< 1, 2, 3, 4, 5, 6, 7, 8, 9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_15606902097717000 == 
3
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_15606902097729000 ==
[](output # MESSAGE)
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 01:03:29 NZST 2019 by jb567
