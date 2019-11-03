---- MODULE MC ----
EXTENDS EagerVoting, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Value
const_156757100300568000 == 
{v1, v2}
----

\* MV CONSTANT definitions Acceptor
const_156757100300569000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_156757100300570000 == 
Permutations(const_156757100300568000) \union Permutations(const_156757100300569000)
----

\* CONSTANT definitions @modelParameterConstants:0Quorum
const_156757100300571000 == 
{{p1, p2}, {p1, p3}, {p2, p3}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_156757100300572000 ==
1..2
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_156757100300573000 ==
C!Spec
----
=============================================================================
\* Modification History
\* Created Wed Sep 04 12:23:23 CST 2019 by pure_
