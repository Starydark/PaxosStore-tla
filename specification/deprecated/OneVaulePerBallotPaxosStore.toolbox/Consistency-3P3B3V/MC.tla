---- MODULE MC ----
EXTENDS OneVaulePerBallotPaxosStore, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions Participant
const_156498943748619000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_156498943748620000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_156498943748621000 == 
Permutations(const_156498943748619000) \union Permutations(const_156498943748620000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_156498943748623000 ==
0 .. 2
----
=============================================================================
\* Modification History
\* Created Mon Aug 05 15:17:17 CST 2019 by hengxin
