----------------------------- MODULE EagerVotingStuttering -----------------------------
EXTENDS EagerVoting
------------------------------------------------------------------------------
top == [top |-> "top"]

VARIABLES s
vars == <<maxBal, votes>>

InitS == Init /\ (s = top)

IncreaseMaxBalStutter(a, b) ==
    IF s = top
        THEN /\ IncreaseMaxBal(a, b)
             /\ s' = s
        ELSE /\ UNCHANGED vars
             /\ s' = s
       
VoteForPostStutter(a, b, v) ==
    IF s = top 
       THEN /\ VoteFor(a, b, v)
            /\ s' = IF b # maxBal'[a]
                      THEN [acc |-> a, val |-> b]
                      ELSE top
       ELSE /\ UNCHANGED vars
            /\ s' = top

-----------------------------------------------------------------------------
NextS == 
    \E a \in Acceptor, b \in Ballot : 
        \/ IncreaseMaxBalStutter(a, b)
        \/ \E v \in Value: 
            VoteForPostStutter(a, b, v)

SpecS == InitS /\ [][NextS]_<<votes, maxBal, s>>
------------------------------------------------------------------------------
V == INSTANCE Voting WITH votes <- votes,
                          maxBal <- IF s = top
                                     THEN maxBal
                                     ELSE [a \in Acceptor |->
                                                IF a = s.acc
                                                  THEN s.val
                                                  ELSE maxBal[a]]            

THEOREM RefinementS == SpecS => V!Spec
==============================================================================