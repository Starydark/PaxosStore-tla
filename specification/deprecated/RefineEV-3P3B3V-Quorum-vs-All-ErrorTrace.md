1: <Initial predicate>
/\ msgs = {}
/\ votes = (p1 :> {} @@ p2 :> {} @@ p3 :> {})
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

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
2: <PrepareV line 20, col 5 to line 21, col 22 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ] }
/\ votes = (p1 :> {} @@ p2 :> {} @@ p3 :> {})
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

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
3: <OnMessageV line 30, col 5 to line 37, col 30 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ] }
/\ votes = (p1 :> {} @@ p2 :> {} @@ p3 :> {})
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

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
4: <OnMessageV line 30, col 5 to line 37, col 30 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ] }
/\ votes = (p1 :> {} @@ p2 :> {} @@ p3 :> {})
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

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
5: <AcceptV line 40, col 5 to line 41, col 55 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {} @@ p3 :> {})
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

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
6: <PrepareV line 20, col 5 to line 21, col 22 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {} @@ p3 :> {})
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
7: <OnMessageV line 30, col 5 to line 37, col 30 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {} @@ p3 :> {})
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
8: <OnMessageV line 30, col 5 to line 37, col 30 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {} @@ p3 :> {})
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
9: <AcceptV line 40, col 5 to line 41, col 55 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {<<1, v2>>} @@ p3 :> {})
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
10: <PrepareV line 20, col 5 to line 21, col 22 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {<<1, v2>>} @@ p3 :> {})
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
11: <OnMessageV line 30, col 5 to line 37, col 30 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p3},
    from |-> p1 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {<<1, v2>>} @@ p3 :> {})
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
12: <OnMessageV line 30, col 5 to line 37, col 30 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p3},
    from |-> p1 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {<<1, v2>>} @@ p3 :> {})
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
13: <OnMessageV line 30, col 5 to line 37, col 30 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p3},
    from |-> p1 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {<<1, v2>>} @@ p3 :> {})
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
14: <AcceptV line 40, col 5 to line 41, col 55 of module UniversalPaxosStoreWithVotes>
/\ msgs = { [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p2},
    from |-> p3 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p2 ],
  [ state |->
        ( p1 :> [maxBal |-> 0, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p1, p2, p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
          p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ),
    to |-> {p3},
    from |-> p1 ],
  [ state |->
        ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
          p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
          p3 :> [maxBal |-> 2, maxVBal |-> 2, maxVVal |-> v2] ),
    to |-> {p1, p2, p3},
    from |-> p3 ] }
/\ votes = (p1 :> {<<0, v1>>} @@ p2 :> {<<1, v2>>} @@ p3 :> {<<2, v2>>})
/\ state = ( p1 :>
      ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p3 :> [maxBal |-> 2, maxVBal |-> -1, maxVVal |-> None] ) @@
  p2 :>
      ( p1 :> [maxBal |-> 0, maxVBal |-> -1, maxVVal |-> None] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 1, maxVBal |-> -1, maxVVal |-> None] ) @@
  p3 :>
      ( p1 :> [maxBal |-> 2, maxVBal |-> 0, maxVVal |-> v1] @@
        p2 :> [maxBal |-> 1, maxVBal |-> 1, maxVVal |-> v2] @@
        p3 :> [maxBal |-> 2, maxVBal |-> 2, maxVVal |-> v2] ) )