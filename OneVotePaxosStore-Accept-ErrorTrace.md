1: <Initial predicate> (Init)
/\ state = ( p1 :>
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
/\ msgs = {}
/\ __trace_var_1564561810320281000 = {}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@ (p1 Prepare)
2: <next_1564561810320283000 line 350, col 3 to line 391, col 2 of module TE>
/\ state = ( p1 :>
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
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ] }
/\ __trace_var_1564561810320281000 = {}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@ (p2 OnMessage from p1)
3: <next_1564561810320283000 line 393, col 3 to line 445, col 2 of module TE>
/\ state = ( p1 :>
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
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1} ] }
/\ __trace_var_1564561810320281000 = {}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@ (p1 OnMessage from p2)
4: <next_1564561810320283000 line 447, col 3 to line 505, col 2 of module TE>
/\ state = ( p1 :>
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
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1} ] }
/\ __trace_var_1564561810320281000 = {}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@ (p1 Accept (0, v1))
5: <next_1564561810320283000 line 507, col 3 to line 571, col 2 of module TE>
/\ state = ( p1 :>
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
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ] }
/\ __trace_var_1564561810320281000 = {}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@ (p2 Accept (0, v2))
6: <next_1564561810320283000 line 573, col 3 to line 649, col 2 of module TE>
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
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
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ] }
/\ __trace_var_1564561810320281000 = {}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@ (p1 OnMessage from p2)
7: <next_1564561810320283000 line 651, col 3 to line 739, col 2 of module TE>
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p2} ] }
/\ __trace_var_1564561810320281000 = {}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@ (p1 Accept (0, v2); it changes (0, 0, v1) to (0, 0, v2))
8: <next_1564561810320283000 line 741, col 3 to line 841, col 2 of module TE>
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p2} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ] }
/\ __trace_var_1564561810320281000 = {v2}

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@ (p3 OnMessage from p1)
9: <next_1564561810320283000 line 843, col 3 to line 955, col 2 of module TE>
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] ) )
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p2,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] ),
    from |-> p3,
    to |-> {p1} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p2} ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p2 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v2] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    from |-> p1,
    to |-> {p1, p2, p3} ] }
/\ __trace_var_1564561810320281000 = {v1, v2}