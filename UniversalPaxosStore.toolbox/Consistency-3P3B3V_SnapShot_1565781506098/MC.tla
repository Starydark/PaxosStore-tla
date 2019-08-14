---- MODULE MC ----
EXTENDS UniversalPaxosStore, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions Participant
const_1565779600330407000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_1565779600330408000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1565779600330409000 == 
Permutations(const_1565779600330407000) \union Permutations(const_1565779600330408000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1565779600330411000 ==
0 .. 2
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 18:46:40 CST 2019 by hengxin
