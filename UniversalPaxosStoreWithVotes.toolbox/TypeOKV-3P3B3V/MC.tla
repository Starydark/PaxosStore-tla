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
const_1565769428495323000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_1565769428495324000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1565769428495325000 == 
Permutations(const_1565769428495323000) \union Permutations(const_1565769428495324000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1565769428495327000 ==
0 .. 2
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 15:57:08 CST 2019 by hengxin
