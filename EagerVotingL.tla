---------------------------- MODULE EagerVotingL ----------------------------
(*
ERROR: The THEOREM in this module does NOT hold:
ShowsSafeAt(Q, b, v) may hold in EagerVoting
but not in Voting with lazyMaxBal <- maxBal.
*)
EXTENDS EagerVoting
-----------------------------------------------------------------------------
VARIABLE lazyMaxBal

TypeOKL == 
    /\ TypeOK
    /\ lazyMaxBal \in [Acceptor -> Ballot \cup {-1}]
-----------------------------------------------------------------------------
InitL == 
    /\ Init
    /\ lazyMaxBal = [a \in Acceptor |-> -1]

IncreaseMaxBalL(a, b) == 
    /\ IncreaseMaxBal(a, b)
    /\ lazyMaxBal' = [lazyMaxBal EXCEPT ![a] = b]

VoteForL(a, b, v) == 
    /\ VoteFor(a, b, v)
    /\ lazyMaxBal' = [lazyMaxBal EXCEPT ![a] = b]
-----------------------------------------------------------------------------
NextL == 
    \E a \in Acceptor, b \in Ballot : 
        \/ IncreaseMaxBalL(a, b)
        \/ \E v \in Value : VoteForL(a, b, v)

SpecL == InitL /\ [][NextL]_<<votes, maxBal, lazyMaxBal>>
-----------------------------------------------------------------------------
V == INSTANCE Voting WITH maxBal <- lazyMaxBal

THEOREM SpecL => V!Spec
=============================================================================
\* Modification History
\* Last modified Wed Aug 14 10:33:29 CST 2019 by hengxin
\* Created Tue Aug 13 20:16:36 CST 2019 by hengxin