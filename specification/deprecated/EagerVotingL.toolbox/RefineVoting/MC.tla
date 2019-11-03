---- MODULE MC ----
EXTENDS EagerVotingL, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Value
const_1565702948807165000 == 
{v1, v2}
----

\* MV CONSTANT definitions Acceptor
const_1565702948807166000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_1565702948807167000 == 
Permutations(const_1565702948807165000) \union Permutations(const_1565702948807166000)
----

\* CONSTANT definitions @modelParameterConstants:0Quorum
const_1565702948807168000 == 
{{a1, a2}, {a1, a3}, {a2, a3}, {a1, a2, a3}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1565702948808169000 ==
0 .. 2
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1565702948808170000 ==
V!Spec
----
=============================================================================
\* Modification History
\* Created Tue Aug 13 21:29:08 CST 2019 by hengxin
