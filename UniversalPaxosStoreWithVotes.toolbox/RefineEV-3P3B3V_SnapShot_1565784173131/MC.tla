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
const_1565781865997437000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_1565781865997438000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1565781865997439000 == 
Permutations(const_1565781865997437000) \union Permutations(const_1565781865997438000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1565781865997441000 ==
0 .. 2
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1565781865998442000 ==
EV!Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 19:24:25 CST 2019 by hengxin
