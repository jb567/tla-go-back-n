---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156069405402536000 == 
<< 1, 2, 3, 4, 5, 6, 7, 8, 9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156069405402537000 == 
3
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_156069405402539000 ==
Tcp!Spec
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 02:07:34 NZST 2019 by jb567
