---- MODULE MC ----
EXTENDS EagerVoting, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Value
const_1565750385441200000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Acceptor
const_1565750385441201000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_1565750385441202000 == 
Permutations(const_1565750385441200000) \union Permutations(const_1565750385441201000)
----

\* CONSTANT definitions @modelParameterConstants:0Quorum
const_1565750385441203000 == 
{{a1, a2}, {a1, a3}, {a2, a3}, {a1, a2, a3}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1565750385441204000 ==
0 .. 2
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 10:39:45 CST 2019 by hengxin
