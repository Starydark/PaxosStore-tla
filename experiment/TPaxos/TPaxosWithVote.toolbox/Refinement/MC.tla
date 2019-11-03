---- MODULE MC ----
EXTENDS TPaxosRefVoting, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Participant
const_156757097313354000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_156757097313355000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_156757097313356000 == 
Permutations(const_156757097313354000) \union Permutations(const_156757097313355000)
----

\* CONSTANT definitions @modelParameterConstants:0Quorum
const_156757097313357000 == 
{{p1, p2}, {p1, p3}, {p2, p3}}
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_156757097313359000 ==
1..2
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_156757097313460000 ==
V!Spec
----
=============================================================================
\* Modification History
\* Created Wed Sep 04 12:22:53 CST 2019 by pure_
