---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156076444083245000 == 
<< 1, 2, 3, 4, 5, 6, 7, 8, 9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156076444083246000 == 
3
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_156076444083248000 ==
Tcp!Spec
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 21:40:40 NZST 2019 by jb567
