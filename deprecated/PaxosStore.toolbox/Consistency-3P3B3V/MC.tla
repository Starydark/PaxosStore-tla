---- MODULE MC ----
EXTENDS PaxosStore, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions Participant
const_156446353257919000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_156446353257920000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_156446353257921000 == 
Permutations(const_156446353257919000) \union Permutations(const_156446353257920000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_156446353257923000 ==
0 .. 2
----
=============================================================================
\* Modification History
\* Created Tue Jul 30 13:12:12 CST 2019 by hengxin
