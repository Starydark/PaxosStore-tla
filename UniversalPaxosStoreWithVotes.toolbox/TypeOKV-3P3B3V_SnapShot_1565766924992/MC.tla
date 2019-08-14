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
const_1565766917554311000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_1565766917554312000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1565766917554313000 == 
Permutations(const_1565766917554311000) \union Permutations(const_1565766917554312000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1565766917554315000 ==
0 .. 2
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 15:15:17 CST 2019 by hengxin
