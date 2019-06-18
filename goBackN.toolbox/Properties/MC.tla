---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156085260628028000 == 
<< 1, 2, 3, 4, 5, 6, 7, 8, 9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156085260628029000 == 
3
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_156085260628031000 ==
Tcp!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_156085260628032000 ==
multiplace!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jun 18 22:10:06 NZST 2019 by jb567
