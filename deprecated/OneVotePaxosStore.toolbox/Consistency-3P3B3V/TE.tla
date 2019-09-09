\* :1:__trace_var_1564564193302299000:chosen"$!@$!@$!@$!@$!"
---- MODULE TE ----
EXTENDS OneVotePaxosStore, TLC, Integers

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions Participant
const_1564564193337302000 == 
{p1, p2, p3}
----

\* MV CONSTANT definitions Value
const_1564564193337303000 == 
{v1, v2, v3}
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1564564193337305000 ==
0 .. 2
----
\* TRACE EXPLORER identifier definition @_TETrace
_TETrace ==
<<
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> {}]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> { [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> { [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> { [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> { [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> { [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> { [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> { [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> { [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ), msgs |-> { [ from |-> p1,
    to |-> {p2},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }]),
([ state |-> ( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] ) ), msgs |-> { [ from |-> p1,
    to |-> {p2},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p3,
    to |-> {p2},
    state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] ) ] }])
>>
----

\* TRACE EXPLORER Position identifier definition @_TEPosition
_TEPosition ==
IF TLCGet("level") >= 11 THEN 11 ELSE TLCGet("level") + 1
----

\* TRACE EXPLORER variable declaration @traceExploreExpressions
VARIABLES __trace_var_1564564193302299000
----

\* TRACE INIT definitiontraceExploreInit
init_1564564193303300000 ==
 state = (
( p1 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{}
)/\
__trace_var_1564564193302299000 = (
chosen
)
----

\* TRACE NEXT definitiontraceExploreNext
next_1564564193303301000 ==
( state = (
( p1 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{}
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
\/
( state = (
( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
\/
( state = (
( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
\/
( state = (
( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
\/
( state = (
( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
\/
( state = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
\/
( state = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
\/
( state = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
\/
( state = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{ [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p2},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
\/
( state = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
)/\
 msgs = (
{ [ from |-> p1,
    to |-> {p2},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ] }
)/\
 state' = (
( p1 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] ) )
)/\
 msgs' = (
{ [ from |-> p1,
    to |-> {p2},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p1,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p2,
    to |-> {p1, p2, p3},
    state |->
        ( p1 :> [maxBal |-> 1, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v1] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) ],
  [ from |-> p3,
    to |-> {p2},
    state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] ) ] }
)/\
__trace_var_1564564193302299000' = (
chosen
)')
----

=============================================================================
\* Modification History
\* Created Wed Jul 31 17:09:53 CST 2019 by hengxin
