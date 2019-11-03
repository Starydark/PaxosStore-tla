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
const_1565781850401431000 == 
{p1, p2}
----

\* MV CONSTANT definitions Value
const_1565781850401432000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1565781850401433000 == 
Permutations(const_1565781850401431000) \union Permutations(const_1565781850401432000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1565781850402435000 ==
0 .. 1
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1565781850403436000 ==
EV!Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 19:24:10 CST 2019 by hengxin
