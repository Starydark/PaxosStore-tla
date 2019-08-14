---- MODULE MC ----
EXTENDS UniversalPaxosStoreWithVotes, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Participant
const_1565770023825335000 == 
{p1, p2}
----

\* MV CONSTANT definitions Value
const_1565770023825336000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1565770023825337000 == 
Permutations(const_1565770023825335000) \union Permutations(const_1565770023825336000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1565770023825339000 ==
0 .. 1
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1565770023826340000 ==
EV!Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 16:07:03 CST 2019 by hengxin
