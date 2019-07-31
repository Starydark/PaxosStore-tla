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
const_1564555822354233000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_1564555822354234000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1564555822354235000 == 
Permutations(const_1564555822354233000) \union Permutations(const_1564555822354234000)
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1564555822354237000 ==
0 .. 2
----
=============================================================================
\* Modification History
\* Created Wed Jul 31 14:50:22 CST 2019 by hengxin
