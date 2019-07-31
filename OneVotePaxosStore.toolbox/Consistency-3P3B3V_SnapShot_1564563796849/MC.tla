---- MODULE MC ----
EXTENDS OneVotePaxosStore, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions Participant
const_1564562182891288000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_1564562182891289000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1564562182891290000 == 
Permutations(const_1564562182891288000) \union Permutations(const_1564562182891289000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1564562182891292000 ==
0 .. 2
----
=============================================================================
\* Modification History
\* Created Wed Jul 31 16:36:22 CST 2019 by hengxin
