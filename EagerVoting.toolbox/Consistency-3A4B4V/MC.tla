---- MODULE MC ----
EXTENDS EagerVoting, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3, v4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Value
const_1565750473333212000 == 
{v1, v2, v3, v4}
----

\* MV CONSTANT definitions Acceptor
const_1565750473333213000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_1565750473333214000 == 
Permutations(const_1565750473333212000) \union Permutations(const_1565750473333213000)
----

\* CONSTANT definitions @modelParameterConstants:0Quorum
const_1565750473333215000 == 
{{a1, a2}, {a1, a3}, {a2, a3}, {a1, a2, a3}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1565750473333216000 ==
0 .. 3
----
=============================================================================
\* Modification History
\* Created Wed Aug 14 10:41:13 CST 2019 by hengxin
