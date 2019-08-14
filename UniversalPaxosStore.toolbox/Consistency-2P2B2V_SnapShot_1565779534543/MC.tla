---- MODULE MC ----
EXTENDS UniversalPaxosStore, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Participant
const_1565779513744395000 == 
{p1, p2}
----

\* MV CONSTANT definitions Value
const_1565779513744396000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1565779513744397000 == 
Permutations(const_1565779513744395000) \union Permutations(const_1565779513744396000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1565779513744399000 ==
0 .. 1
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 18:45:13 CST 2019 by hengxin
