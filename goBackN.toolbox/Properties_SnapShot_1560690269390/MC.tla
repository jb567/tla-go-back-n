---- MODULE MC ----
EXTENDS ass3, TLC

\* CONSTANT definitions @modelParameterConstants:0MESSAGE
const_156069026494810000 == 
<< 1, 2, 3, 4, 5, 6, 7, 8, 9>>
----

\* CONSTANT definitions @modelParameterConstants:1WINDOW_SIZE
const_156069026494811000 == 
3
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_156069026494913000 ==
[](output # MESSAGE)
----
=============================================================================
\* Modification History
\* Created Mon Jun 17 01:04:24 NZST 2019 by jb567
