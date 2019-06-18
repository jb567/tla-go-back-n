---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_15608518750922000 == 
<< 1, 2, 3, 4, 5, 6, 7, 8, 9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_15608518750923000 == 
3
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_15608518750935000 ==
Tcp!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jun 18 21:57:55 NZST 2019 by jb567
