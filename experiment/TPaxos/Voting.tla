------------------------------- MODULE Voting -------------------------------
EXTENDS Integers, FiniteSets, TLAPS
-----------------------------------------------------------------------------
CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
Ballot == Nat

VARIABLES votes, maxBal

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
-----------------------------------------------------------------------------
VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

ShowsSafeAt(Q, b, v) == /\ \A a \in Q : maxBal[a] \geq b \* have promised
                        /\ \E c \in -1..(b-1) :
                            /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
                            /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)      
OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
        VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) == \E Q \in Quorum : 
                                \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value : 
                    VotedFor(a, b, v) => SafeAt(b, v)
-----------------------------------------------------------------------------
Init == /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) == /\ b > maxBal[a]
                        /\ maxBal' = [maxBal EXCEPT ![a] = b] \* make promise
                        /\ UNCHANGED votes

VoteFor(a, b, v) == /\ maxBal[a] <= b \* keep promise
                    /\ \A vt \in votes[a] : vt[1] # b
                    /\ \A c \in Acceptor \ {a} :
                        \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
                    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v) \* safe to vote
                    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}] \* vote
                    /\ maxBal' = [maxBal EXCEPT ![a] = b] \* make promise
-----------------------------------------------------------------------------
Next == \E a \in Acceptor, b \in Ballot : 
                \/ IncreaseMaxBal(a, b)
                \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>
-----------------------------------------------------------------------------

------------------------------------------------------------------------------
ChosenAt(b, v) == 
    \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Consistency == chosen = {} \/ \E v \in Value : chosen = {v} \* Cardinality(chosen) <= 1
---------------------------------------------------------------------------

OneVote == 
    \A a \in Acceptor, b \in Ballot, v, w \in Value : 
        VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)


Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot
-----------------------------------------------------------------------------
THEOREM AllSafeAtZero == \A v \in Value : SafeAt(0, v)
  BY DEF SafeAt

THEOREM ChoosableThm ==
          \A b \in Ballot, v \in Value :
             ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
  BY DEF ChosenAt, NoneOtherChoosableAt

THEOREM OneVoteThm == OneValuePerBallot => OneVote
  BY DEF OneValuePerBallot, OneVote
-----------------------------------------------------------------------------
THEOREM VotesSafeImpliesConsistency ==
   ASSUME VotesSafe, OneVote, chosen # {}
   PROVE  \E v \in Value : chosen = {v}
<1>1. PICK v \in Value : v \in chosen
  BY DEF chosen
<1>2. SUFFICES ASSUME NEW w \in chosen
               PROVE  w = v
  BY <1>1, <1>2
<1>3. ASSUME NEW b1 \in Ballot, NEW b2 \in Ballot, b1 < b2,
             NEW v1 \in Value, NEW v2 \in Value,
             ChosenAt(b1, v1) /\ ChosenAt(b2, v2)
      PROVE  v1 = v2
  <2>1. SafeAt(b2, v2)
    BY <1>3, QuorumAssumption, SMT DEF ChosenAt, VotesSafe
  <2>2. QED
    BY <1>3, <2>1, QuorumAssumption, Z3
    DEFS CannotVoteAt, DidNotVoteAt, OneVote, 
         ChosenAt, NoneOtherChoosableAt, Ballot, SafeAt
<1>4. QED
  BY QuorumAssumption, <1>1, <1>2, <1>3, Z3 
  DEFS Ballot, ChosenAt, OneVote, chosen

THEOREM ShowsSafety ==
          TypeOK /\ VotesSafe /\ OneValuePerBallot =>
             \A Q \in Quorum, b \in Ballot, v \in Value :
               ShowsSafeAt(Q, b, v) => SafeAt(b, v)
  BY QuorumAssumption, Z3
  DEFS Ballot, TypeOK, VotesSafe, OneValuePerBallot, SafeAt, 
    ShowsSafeAt, CannotVoteAt, NoneOtherChoosableAt, DidNotVoteAt
    
THEOREM SafeAtStable == Inv /\ Next /\ TypeOK' =>
                            \A b \in Ballot, v \in Value :
                                SafeAt(b, v) => SafeAt(b, v)'
  OMITTED                                
-----------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv
<1> USE DEF Inv
<1>1. Init => Inv
  BY DEF Init, TypeOK, VotesSafe, OneValuePerBallot, VotedFor 
<1>2. Inv /\ [Next]_<<votes, maxBal>> => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_<<votes, maxBal>>
               PROVE  Inv'
    OBVIOUS               
  <2>1. CASE Next
    <3> SUFFICES ASSUME NEW a \in Acceptor, NEW b \in Ballot,
                        \/ IncreaseMaxBal(a, b)
                        \/ \E v \in Value : VoteFor(a, b, v)
                 PROVE  Inv'
      BY <2>1 DEF Next
    <3>1. CASE IncreaseMaxBal(a, b)
      <4>1. TypeOK'
        BY <3>1 DEF TypeOK, IncreaseMaxBal
      <4>2. VotesSafe'
        <5> SUFFICES ASSUME NEW a_1 \in Acceptor', NEW b_1 \in Ballot', NEW v \in Value'
                     PROVE  VotedFor(a_1, b_1, v)' => SafeAt(b_1, v)'
          BY DEF VotesSafe
        <5>1. \A aa \in Acceptor, bb \in Ballot, vv \in Value :
                VotedFor(aa, bb, vv) <=> VotedFor(aa, bb, vv)'
          BY <3>1 DEF IncreaseMaxBal, VotedFor
        <5>2. \A aa \in Acceptor, bb \in Ballot :
                maxBal[aa] > bb => maxBal'[aa] > bb
          BY <3>1 DEF IncreaseMaxBal, TypeOK, Ballot
        <5>3. \A aa \in Acceptor, bb \in Ballot :
                DidNotVoteAt(aa, bb) => DidNotVoteAt(aa, bb)'
          BY <3>1 DEF IncreaseMaxBal, DidNotVoteAt, VotedFor
        <5>4. \A aa \in Acceptor, bb \in Ballot :
                CannotVoteAt(aa, bb) => CannotVoteAt(aa, bb)'
          BY <3>1, <5>2, <5>3 DEF IncreaseMaxBal, CannotVoteAt
        <5>5. \A bb \in Ballot, vv \in Value :
                NoneOtherChoosableAt(bb, vv) => NoneOtherChoosableAt(bb, vv)'
          BY <5>1, <5>4, QuorumAssumption DEFS NoneOtherChoosableAt                
        <5>6. QED
          BY <5>1, <5>5 DEF TypeOK, Ballot, VotesSafe, SafeAt
      <4>3. OneValuePerBallot'
        BY <3>1 DEF IncreaseMaxBal, OneValuePerBallot, VotedFor
      <4>4. QED
        BY <4>1, <4>2, <4>3 DEF Inv
    <3>2. ASSUME NEW v \in Value,
                 VoteFor(a, b, v)
          PROVE  Inv'
      <4> SUFFICES ASSUME NEW Q \in Quorum,
                          ShowsSafeAt(Q, b, v)
                   PROVE  Inv'
        BY <3>2 DEF VoteFor
      <4>1. TypeOK'
        BY <3>2 DEF TypeOK, VoteFor
      <4>2. VotesSafe' \* Using OneValuePerBallot in SafeAtStable
        <5> SUFFICES ASSUME NEW aa \in Acceptor', NEW bb \in Ballot', NEW vv \in Value',
                            VotedFor(aa, bb, vv)'
                     PROVE  SafeAt(bb, vv)'
          BY DEF VotesSafe
        <5>1. CASE VotedFor(aa, bb, vv)
          <6>1. SafeAt(bb, vv)
            BY <5>1 DEF VotesSafe
          <6> QED
            BY <4>1, <6>1, SafeAtStable DEF Next
        <5>2. CASE ~VotedFor(aa, bb, vv)
          <6>1. aa = a /\ bb = b /\ vv = v /\ VotedFor(a, b, v)'
            BY <3>2, <4>1, <5>2 DEF VoteFor, VotedFor, TypeOK
          <6> QED
            BY <4>1, <6>1, ShowsSafety, SafeAtStable DEF VoteFor, Next
        <5> QED
          BY <5>1, <5>2
      <4>3. OneValuePerBallot'
        BY <3>2 DEF VoteFor, OneValuePerBallot, VotedFor, TypeOK
      <4>4. QED
        BY <3>2, <4>1, <4>2, <4>3 DEF Inv
    <3>3. QED
      BY <2>1, <3>1, <3>2
  <2>2. CASE UNCHANGED <<votes, maxBal>>
    BY <2>2 
    DEFS TypeOK, Next, VotesSafe, OneValuePerBallot, 
         VotedFor, SafeAt, NoneOtherChoosableAt, CannotVoteAt, DidNotVoteAt, 
         IncreaseMaxBal, VoteFor
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
----------------------------------------------------------------------------
THEOREM Consistent == Spec => []Consistency
<1> USE DEF Ballot
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv
               PROVE  Consistency
    OBVIOUS
  <2> QED
    BY VotesSafeImpliesConsistency, OneVoteThm DEF Inv, Consistency
<1>2. QED
  BY Invariant, <1>1, PTL
----------------------------------------------------------------------------
C == INSTANCE Consensus \* WITH chosen <- chosen

THEOREM Refinement == Spec => C!Spec
<1>1. Init => C!Init
  BY QuorumAssumption, SetExtensionality, IsaM("force")
  DEF Init, C!Init, chosen, ChosenAt, VotedFor
<1>2. TypeOK' /\ Consistency' /\ [Next]_<<votes, maxBal>> => [C!Next]_chosen
  <2>1. UNCHANGED <<votes, maxBal>> => UNCHANGED chosen
    BY DEF chosen, ChosenAt, VotedFor
  <2>2. TypeOK' /\ Consistency' /\ Next => C!Next \/ UNCHANGED chosen
    <3>1. SUFFICES ASSUME TypeOK', Consistency', Next
                   PROVE  C!Next \/ UNCHANGED chosen
      OBVIOUS
    <3>2. chosen \subseteq chosen' 
      BY <3>1, QuorumAssumption, Z3
      DEFS Next, IncreaseMaxBal, VoteFor, Inv, TypeOK, chosen, ChosenAt, VotedFor, Ballot
    <3>3. chosen' = {} \/ \E v \in Value : chosen' = {v} 
      BY <3>1 DEF Consistency
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF C!Next
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, Invariant, Consistent, PTL DEF Spec, Inv, C!Spec
=============================================================================