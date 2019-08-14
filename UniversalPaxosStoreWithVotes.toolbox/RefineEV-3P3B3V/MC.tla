---- MODULE MC ----
EXTENDS UniversalPaxosStoreWithVotes, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions Participant
const_1565784544801443000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_1565784544801444000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1565784544801445000 == 
Permutations(const_1565784544801443000) \union Permutations(const_1565784544801444000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1565784544801447000 ==
0 .. 2
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1565784544802448000 ==
EV!Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 20:09:04 CST 2019 by hengxin
