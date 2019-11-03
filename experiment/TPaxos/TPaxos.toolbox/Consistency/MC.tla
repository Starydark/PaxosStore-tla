---- MODULE MC ----
EXTENDS TPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Participant
const_156757074807030000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_156757074807031000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_156757074807032000 == 
Permutations(const_156757074807030000) \union Permutations(const_156757074807031000)
----

\* CONSTANT definitions @modelParameterConstants:2Quorum
const_156757074807033000 == 
{{p1, p2}, {p1, p3}, {p2, p3}}
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_156757074807035000 ==
1..2
----
=============================================================================
\* Modification History
\* Created Wed Sep 04 12:19:08 CST 2019 by pure_
