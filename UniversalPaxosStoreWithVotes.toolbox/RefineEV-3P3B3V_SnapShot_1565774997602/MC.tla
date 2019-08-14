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
const_1565772713880389000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_1565772713880390000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1565772713880391000 == 
Permutations(const_1565772713880389000) \union Permutations(const_1565772713880390000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1565772713880393000 ==
0 .. 2
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1565772713881394000 ==
EV!Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 16:51:53 CST 2019 by hengxin
