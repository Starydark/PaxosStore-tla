(* automatically generated -- do not edit manually *)
theory EagerVoting imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'59:
(* usable definition PropositionalTemporalLogic suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsBijection suppressed *)
(* usable definition IsFiniteSet suppressed *)
fixes Cardinality
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition TypeOK suppressed *)
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteAt suppressed *)
(* usable definition ShowsSafeAt suppressed *)
(* usable definition Init suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ChosenAt suppressed *)
(* usable definition chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition NoneOtherChoosableAt suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition VotesSafe suppressed *)
(* usable definition OneVote suppressed *)
(* usable definition OneValuePerBallot suppressed *)
assumes v'85: "(((((TypeOK) \<and> (VotesSafe))) \<and> (OneValuePerBallot)))"
assumes v'86: "(((Next) \<or> (((((a_voteshash_primea :: c)) = (votes))) & ((((a_maxBalhash_primea :: c)) = (maxBal))))))"
fixes a
assumes a_in : "(a \<in> (Acceptor))"
fixes b
assumes b_in : "(b \<in> (Ballot))"
assumes v'94: "((((greater ((b), (fapply ((maxBal), (a)))))) & ((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (b)]))) & ((((a_voteshash_primea :: c)) = (votes)))) | (\<exists> v \<in> (Value) : ((VoteFor ((a), (b), (v))))))"
fixes a_aunde_1a
assumes a_aunde_1a_in : "(a_aunde_1a \<in> (Acceptor))"
fixes a_bunde_1a
assumes a_bunde_1a_in : "(a_bunde_1a \<in> (Ballot))"
fixes v
assumes v_in : "(v \<in> (Value))"
assumes v'113: "((greater ((b), (fapply ((maxBal), (a))))))"
assumes v'114: "((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (b)])))"
assumes v'115: "((((a_voteshash_primea :: c)) = (votes)))"
assumes v'116: "(\<forall> aa \<in> (Acceptor) : (\<forall> bb \<in> (Ballot) : ((((greater ((fapply ((maxBal), (aa))), (bb)))) \<Rightarrow> ((greater ((fapply (((a_maxBalhash_primea :: c)), (aa))), (bb))))))))"
assumes v'117: "(\<forall> aa \<in> (Acceptor) : (\<forall> bb \<in> (Ballot) : ((((DidNotVoteAt ((aa), (bb)))) \<Rightarrow> ((a_h1902b51376fdd3dbe69d9995bcf047a ((aa), (bb)) :: c))))))"
shows "(\<forall> aa \<in> (Acceptor) : (\<forall> bb \<in> (Ballot) : (((((greater ((fapply ((maxBal), (aa))), (bb)))) & ((DidNotVoteAt ((aa), (bb))))) \<Rightarrow> (((greater ((fapply (((a_maxBalhash_primea :: c)), (aa))), (bb)))) & ((a_h1902b51376fdd3dbe69d9995bcf047a ((aa), (bb)) :: c)))))))"(is "PROP ?ob'59")
proof -
ML_command {* writeln "*** TLAPS ENTER 59"; *}
show "PROP ?ob'59"

(* BEGIN ZENON INPUT
;; file=EagerVoting.tlaps/tlapm_e8ea85.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >EagerVoting.tlaps/tlapm_e8ea85.znn.out
;; obligation #59
$hyp "v'85" (/\ (/\ TypeOK VotesSafe) OneValuePerBallot)
$hyp "v'86" (\/ Next (/\ (= a_voteshash_primea votes) (= a_maxBalhash_primea
maxBal)))
$hyp "a_in" (TLA.in a Acceptor)
$hyp "b_in" (TLA.in b Ballot)
$hyp "v'94" (\/ (/\ (arith.lt (TLA.fapply maxBal a) b) (= a_maxBalhash_primea
(TLA.except maxBal a b)) (= a_voteshash_primea votes))
(TLA.bEx Value ((v) (VoteFor a b
v))))
$hyp "a_aunde_1a_in" (TLA.in a_aunde_1a Acceptor)
$hyp "a_bunde_1a_in" (TLA.in a_bunde_1a Ballot)
$hyp "v_in" (TLA.in v Value)
$hyp "v'113" (arith.lt (TLA.fapply maxBal a)
b)
$hyp "v'114" (= a_maxBalhash_primea
(TLA.except maxBal a b))
$hyp "v'115" (= a_voteshash_primea
votes)
$hyp "v'116" (TLA.bAll Acceptor ((aa) (TLA.bAll Ballot ((bb) (=> (arith.lt bb
(TLA.fapply maxBal aa)) (arith.lt bb
(TLA.fapply a_maxBalhash_primea aa)))))))
$hyp "v'117" (TLA.bAll Acceptor ((aa) (TLA.bAll Ballot ((bb) (=> (DidNotVoteAt aa
bb) (a_h1902b51376fdd3dbe69d9995bcf047a aa
bb))))))
$goal (TLA.bAll Acceptor ((aa) (TLA.bAll Ballot ((bb) (=> (/\ (arith.lt bb
(TLA.fapply maxBal aa)) (DidNotVoteAt aa bb)) (/\ (arith.lt bb
(TLA.fapply a_maxBalhash_primea aa)) (a_h1902b51376fdd3dbe69d9995bcf047a aa
bb)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hl:"bAll(Acceptor, (\<lambda>aa. bAll(Ballot, (\<lambda>bb. ((bb < (maxBal[aa]))=>(bb < (a_maxBalhash_primea[aa])))))))" (is "?z_hl")
 using v'116 by blast
 have z_Hm:"bAll(Acceptor, (\<lambda>aa. bAll(Ballot, (\<lambda>bb. (DidNotVoteAt(aa, bb)=>a_h1902b51376fdd3dbe69d9995bcf047a(aa, bb))))))" (is "?z_hm")
 using v'117 by blast
 assume z_Hn:"(~bAll(Acceptor, (\<lambda>aa. bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[aa]))&DidNotVoteAt(aa, bb))=>((bb < (a_maxBalhash_primea[aa]))&a_h1902b51376fdd3dbe69d9995bcf047a(aa, bb))))))))" (is "~?z_hbi")
 have z_Hbp_z_Hl: "(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. ((bb < (maxBal[x]))=>(bb < (a_maxBalhash_primea[x]))))))) == ?z_hl" (is "?z_hbp == _")
 by (unfold bAll_def)
 have z_Hbp: "?z_hbp" (is "\\A x : ?z_hca(x)")
 by (unfold z_Hbp_z_Hl, fact z_Hl)
 have z_Hcb_z_Hm: "(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (DidNotVoteAt(x, bb)=>a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))) == ?z_hm" (is "?z_hcb == _")
 by (unfold bAll_def)
 have z_Hcb: "?z_hcb" (is "\\A x : ?z_hci(x)")
 by (unfold z_Hcb_z_Hm, fact z_Hm)
 have z_Hcj_z_Hn: "(~(\\A x:((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))) == (~?z_hbi)" (is "?z_hcj == ?z_hn")
 by (unfold bAll_def)
 have z_Hcj: "?z_hcj" (is "~(\\A x : ?z_hcr(x))")
 by (unfold z_Hcj_z_Hn, fact z_Hn)
 have z_Hcs: "(\\E x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))" (is "\\E x : ?z_hcu(x)")
 by (rule zenon_notallex_0 [of "?z_hcr", OF z_Hcj])
 have z_Hcv: "?z_hcu((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))))" (is "~(?z_hcx=>?z_hcy)")
 by (rule zenon_ex_choose_0 [of "?z_hcu", OF z_Hcs])
 have z_Hcx: "?z_hcx"
 by (rule zenon_notimply_0 [OF z_Hcv])
 have z_Hcz: "(~?z_hcy)"
 by (rule zenon_notimply_1 [OF z_Hcv])
 have z_Hda_z_Hcz: "(~(\\A x:((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))))) == (~?z_hcy)" (is "?z_hda == ?z_hcz")
 by (unfold bAll_def)
 have z_Hda: "?z_hda" (is "~(\\A x : ?z_hdn(x))")
 by (unfold z_Hda_z_Hcz, fact z_Hcz)
 have z_Hdo: "(\\E x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))))))" (is "\\E x : ?z_hdq(x)")
 by (rule zenon_notallex_0 [of "?z_hdn", OF z_Hda])
 have z_Hdr: "?z_hdq((CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))))))" (is "~(?z_hdt=>?z_hdu)")
 by (rule zenon_ex_choose_0 [of "?z_hdq", OF z_Hdo])
 have z_Hdt: "?z_hdt"
 by (rule zenon_notimply_0 [OF z_Hdr])
 have z_Hdv: "(~?z_hdu)" (is "~(?z_hdw=>?z_hdx)")
 by (rule zenon_notimply_1 [OF z_Hdr])
 have z_Hdw: "?z_hdw" (is "?z_hdy&?z_hdz")
 by (rule zenon_notimply_0 [OF z_Hdv])
 have z_Hea: "(~?z_hdx)" (is "~(?z_heb&?z_hec)")
 by (rule zenon_notimply_1 [OF z_Hdv])
 have z_Hdy: "?z_hdy"
 by (rule zenon_and_0 [OF z_Hdw])
 have z_Hdz: "?z_hdz"
 by (rule zenon_and_1 [OF z_Hdw])
 show FALSE
 proof (rule zenon_notand [OF z_Hea])
  assume z_Hed:"(~?z_heb)"
  have z_Hee: "?z_hca((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))))" (is "_=>?z_hef")
  by (rule zenon_all_0 [of "?z_hca" "(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))", OF z_Hbp])
  show FALSE
  proof (rule zenon_imply [OF z_Hee])
   assume z_Heg:"(~?z_hcx)"
   show FALSE
   by (rule notE [OF z_Heg z_Hcx])
  next
   assume z_Hef:"?z_hef"
   have z_Heh_z_Hef: "(\\A x:((x \\in Ballot)=>((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))=>(x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))))) == ?z_hef" (is "?z_heh == _")
   by (unfold bAll_def)
   have z_Heh: "?z_heh" (is "\\A x : ?z_hek(x)")
   by (unfold z_Heh_z_Hef, fact z_Hef)
   have z_Hel: "?z_hek((CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))))))" (is "_=>?z_hem")
   by (rule zenon_all_0 [of "?z_hek" "(CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))))))", OF z_Heh])
   show FALSE
   proof (rule zenon_imply [OF z_Hel])
    assume z_Hen:"(~?z_hdt)"
    show FALSE
    by (rule notE [OF z_Hen z_Hdt])
   next
    assume z_Hem:"?z_hem"
    show FALSE
    proof (rule zenon_imply [OF z_Hem])
     assume z_Heo:"(~?z_hdy)"
     show FALSE
     by (rule notE [OF z_Heo z_Hdy])
    next
     assume z_Heb:"?z_heb"
     show FALSE
     by (rule notE [OF z_Hed z_Heb])
    qed
   qed
  qed
 next
  assume z_Hep:"(~?z_hec)"
  have z_Heq: "?z_hci((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))))" (is "_=>?z_her")
  by (rule zenon_all_0 [of "?z_hci" "(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))", OF z_Hcb])
  show FALSE
  proof (rule zenon_imply [OF z_Heq])
   assume z_Heg:"(~?z_hcx)"
   show FALSE
   by (rule notE [OF z_Heg z_Hcx])
  next
   assume z_Her:"?z_her"
   have z_Hes_z_Her: "(\\A x:((x \\in Ballot)=>(DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)=>a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))) == ?z_her" (is "?z_hes == _")
   by (unfold bAll_def)
   have z_Hes: "?z_hes" (is "\\A x : ?z_hev(x)")
   by (unfold z_Hes_z_Her, fact z_Her)
   have z_Hew: "?z_hev((CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x)))))))" (is "_=>?z_hex")
   by (rule zenon_all_0 [of "?z_hev" "(CHOOSE x:(~((x \\in Ballot)=>(((x < (maxBal[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&DidNotVoteAt((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))=>((x < (a_maxBalhash_primea[(CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb))))))))]))&a_h1902b51376fdd3dbe69d9995bcf047a((CHOOSE x:(~((x \\in Acceptor)=>bAll(Ballot, (\<lambda>bb. (((bb < (maxBal[x]))&DidNotVoteAt(x, bb))=>((bb < (a_maxBalhash_primea[x]))&a_h1902b51376fdd3dbe69d9995bcf047a(x, bb)))))))), x))))))", OF z_Hes])
   show FALSE
   proof (rule zenon_imply [OF z_Hew])
    assume z_Hen:"(~?z_hdt)"
    show FALSE
    by (rule notE [OF z_Hen z_Hdt])
   next
    assume z_Hex:"?z_hex"
    show FALSE
    proof (rule zenon_imply [OF z_Hex])
     assume z_Hey:"(~?z_hdz)"
     show FALSE
     by (rule notE [OF z_Hey z_Hdz])
    next
     assume z_Hec:"?z_hec"
     show FALSE
     by (rule notE [OF z_Hep z_Hec])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 59"; *} qed
lemma ob'115:
(* usable definition PropositionalTemporalLogic suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsBijection suppressed *)
(* usable definition IsFiniteSet suppressed *)
fixes Cardinality
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition TypeOK suppressed *)
(* usable definition DidNotVoteAt suppressed *)
(* usable definition ShowsSafeAt suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition CannotVoteAt suppressed *)
(* usable definition NoneOtherChoosableAt suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition VotesSafe suppressed *)
(* usable definition OneVote suppressed *)
(* usable definition OneValuePerBallot suppressed *)
(* usable definition Inv suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!NatInductiveDefHypothesis suppressed *)
(* usable definition C!NatInductiveDefConclusion suppressed *)
(* usable definition C!FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition C!FiniteNatInductiveDefConclusion suppressed *)
(* usable definition C!IsBijection suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!Inv suppressed *)
assumes v'139: "((\<forall> Q \<in> (Quorum) : (((Q) \<subseteq> (Acceptor)))) & (\<forall> a_Q1a \<in> (Quorum) : (\<forall> a_Q2a \<in> (Quorum) : (((((a_Q1a) \<inter> (a_Q2a))) \<noteq> ({}))))))"
assumes v'140: "(\<forall>S : (\<forall>T : (((\<forall>x : (((((x) \<in> (S))) \<Leftrightarrow> (((x) \<in> (T)))))) \<Rightarrow> (((S) = (T)))))))"
shows "((((((votes) = ([ a \<in> (Acceptor)  \<mapsto> ({})]))) & (((maxBal) = ([ a \<in> (Acceptor)  \<mapsto> ((minus (((Succ[0])))))])))) \<Rightarrow> (((subsetOf((Value), %v. (\<exists> b \<in> (Ballot) : (\<exists> Q \<in> (Quorum) : (\<forall> a \<in> (Q) : (((<<(b), (v)>>) \<in> (fapply ((votes), (a)))))))))) = ({})))))"(is "PROP ?ob'115")
proof -
ML_command {* writeln "*** TLAPS ENTER 115"; *}
show "PROP ?ob'115"
using assms by force
ML_command {* writeln "*** TLAPS EXIT 115"; *} qed
lemma ob'123:
(* usable definition PropositionalTemporalLogic suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsBijection suppressed *)
(* usable definition IsFiniteSet suppressed *)
fixes Cardinality
fixes Value
fixes Acceptor
fixes Quorum
(* usable definition Ballot suppressed *)
fixes votes votes'
fixes maxBal maxBal'
(* usable definition TypeOK suppressed *)
(* usable definition VotedFor suppressed *)
(* usable definition DidNotVoteAt suppressed *)
(* usable definition ShowsSafeAt suppressed *)
(* usable definition Init suppressed *)
(* usable definition IncreaseMaxBal suppressed *)
(* usable definition VoteFor suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ChosenAt suppressed *)
(* usable definition chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition CannotVoteAt suppressed *)
(* usable definition NoneOtherChoosableAt suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition VotesSafe suppressed *)
(* usable definition OneVote suppressed *)
(* usable definition OneValuePerBallot suppressed *)
(* usable definition Inv suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!NatInductiveDefHypothesis suppressed *)
(* usable definition C!NatInductiveDefConclusion suppressed *)
(* usable definition C!FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition C!FiniteNatInductiveDefConclusion suppressed *)
(* usable definition C!IsBijection suppressed *)
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!Inv suppressed *)
assumes v'154: "(((a_hef12f5554781c2213604492856f635a :: c)) & ((a_h51861ad69648f81a4743d26221e064a :: c)) & (Next))"
assumes v'155: "(((chosen) \<subseteq> ((h7f4dc7fdc95ffefa185ce3d407a37f :: c))))"
assumes v'156: "((((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) = ({}))) \<or> (\<exists> v \<in> (Value) : ((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) = ({(v)}))))))"
shows "((((((chosen) = ({}))) & (\<exists> v \<in> (Value) : ((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) = ({(v)}))))) \<or> ((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) = (chosen)))))"(is "PROP ?ob'123")
proof -
ML_command {* writeln "*** TLAPS ENTER 123"; *}
show "PROP ?ob'123"

(* BEGIN ZENON INPUT
;; file=EagerVoting.tlaps/tlapm_92ddaf.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >EagerVoting.tlaps/tlapm_92ddaf.znn.out
;; obligation #123
$hyp "v'154" (/\ a_hef12f5554781c2213604492856f635a
a_h51861ad69648f81a4743d26221e064a Next)
$hyp "v'155" (TLA.subseteq chosen
h7f4dc7fdc95ffefa185ce3d407a37f)
$hyp "v'156" (\/ (= h7f4dc7fdc95ffefa185ce3d407a37f TLA.emptyset)
(TLA.bEx Value ((v) (= h7f4dc7fdc95ffefa185ce3d407a37f
(TLA.set v)))))
$goal (\/ (/\ (= chosen TLA.emptyset)
(TLA.bEx Value ((v) (= h7f4dc7fdc95ffefa185ce3d407a37f (TLA.set v)))))
(= h7f4dc7fdc95ffefa185ce3d407a37f
chosen))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"(chosen \\subseteq h7f4dc7fdc95ffefa185ce3d407a37f)" (is "?z_hd")
 using v'155 by blast
 have z_He:"((h7f4dc7fdc95ffefa185ce3d407a37f={})|bEx(Value, (\<lambda>v. (h7f4dc7fdc95ffefa185ce3d407a37f={v}))))" (is "?z_hi|?z_hk")
 using v'156 by blast
 have zenon_L1_: "(\\A x:((x \\in chosen)=>(x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) ==> ((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))) \\in chosen) ==> (~((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))) \\in h7f4dc7fdc95ffefa185ce3d407a37f)) ==> FALSE" (is "?z_hb ==> ?z_hu ==> ?z_hbb ==> FALSE")
 proof -
  assume z_Hb:"?z_hb" (is "\\A x : ?z_hbd(x)")
  assume z_Hu:"?z_hu"
  assume z_Hbb:"?z_hbb" (is "~?z_hbc")
  have z_Hbe: "?z_hbd((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))))"
  by (rule zenon_all_0 [of "?z_hbd" "(CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))", OF z_Hb])
  show FALSE
  proof (rule zenon_imply [OF z_Hbe])
   assume z_Hbf:"(~?z_hu)"
   show FALSE
   by (rule notE [OF z_Hbf z_Hu])
  next
   assume z_Hbc:"?z_hbc"
   show FALSE
   by (rule notE [OF z_Hbb z_Hbc])
  qed
 qed
 have zenon_L2_: "?z_hi ==> (\\A x:((x \\in chosen)=>(x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) ==> FALSE" (is "_ ==> ?z_hb ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hb:"?z_hb" (is "\\A x : ?z_hbd(x)")
  have z_Hbg: "(~(\\A zenon_Vx:((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))" (is "~(\\A x : ?z_hbi(x))")
  by (rule zenon_notsetequal_0 [of "h7f4dc7fdc95ffefa185ce3d407a37f" "chosen", OF z_Hbj])
  have z_Hbk: "(\\E zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))" (is "\\E x : ?z_hbl(x)")
  by (rule zenon_notallex_0 [of "?z_hbi", OF z_Hbg])
  have z_Hbm: "?z_hbl((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))))" (is "~(?z_hbc<=>?z_hu)")
  by (rule zenon_ex_choose_0 [of "?z_hbl", OF z_Hbk])
  show FALSE
  proof (rule zenon_notequiv [OF z_Hbm])
   assume z_Hbb:"(~?z_hbc)"
   assume z_Hu:"?z_hu"
   show FALSE
   by (rule zenon_L1_ [OF z_Hb z_Hu z_Hbb])
  next
   assume z_Hbc:"?z_hbc"
   assume z_Hbf:"(~?z_hu)"
   have z_Hbn: "((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))) \\in {})" (is "?z_hbn")
   by (rule subst [where P="(\<lambda>zenon_Vua. ((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))) \\in zenon_Vua))", OF z_Hi z_Hbc])
   show FALSE
   by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))", OF z_Hbn])
  qed
 qed
 have zenon_L3_: "((CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {})))) \\in {}) ==> FALSE" (is "?z_hbr ==> FALSE")
 proof -
  assume z_Hbr:"?z_hbr"
  show FALSE
  by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {}))))", OF z_Hbr])
 qed
 have zenon_L4_: "(~(\\A zenon_Vx:((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))) ==> (h7f4dc7fdc95ffefa185ce3d407a37f={(CHOOSE x:((x \\in Value)&(h7f4dc7fdc95ffefa185ce3d407a37f={x})))}) ==> ((CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {})))) \\in chosen) ==> bAll(chosen, (\<lambda>x. (x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) ==> (\\A x:((x \\in chosen)=>(x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) ==> FALSE" (is "?z_hbg ==> ?z_hby ==> ?z_hcf ==> ?z_hcg ==> ?z_hb ==> FALSE")
 proof -
  assume z_Hbg:"?z_hbg" (is "~(\\A x : ?z_hbi(x))")
  assume z_Hby:"?z_hby" (is "_=?z_hbz")
  assume z_Hcf:"?z_hcf"
  assume z_Hcg:"?z_hcg"
  assume z_Hb:"?z_hb" (is "\\A x : ?z_hbd(x)")
  have z_Hbk: "(\\E zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))" (is "\\E x : ?z_hbl(x)")
  by (rule zenon_notallex_0 [of "?z_hbi", OF z_Hbg])
  have z_Hbm: "?z_hbl((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))))" (is "~(?z_hbc<=>?z_hu)")
  by (rule zenon_ex_choose_0 [of "?z_hbl", OF z_Hbk])
  show FALSE
  proof (rule zenon_notequiv [OF z_Hbm])
   assume z_Hbb:"(~?z_hbc)"
   assume z_Hu:"?z_hu"
   show FALSE
   by (rule zenon_L1_ [OF z_Hb z_Hu z_Hbb])
  next
   assume z_Hbc:"?z_hbc"
   assume z_Hbf:"(~?z_hu)"
   have z_Hci: "((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))) \\in ?z_hbz)" (is "?z_hci")
   by (rule subst [where P="(\<lambda>zenon_Vua. ((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))) \\in zenon_Vua))", OF z_Hby z_Hbc])
   show FALSE
   proof (rule zenon_in_addElt [of "(CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))" "(CHOOSE x:((x \\in Value)&(h7f4dc7fdc95ffefa185ce3d407a37f={x})))" "{}", OF z_Hci])
    assume z_Hck:"((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))=(CHOOSE x:((x \\in Value)&(h7f4dc7fdc95ffefa185ce3d407a37f={x}))))" (is "?z_hv=?z_hca")
    have z_Hcl: "((CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {})))) \\in h7f4dc7fdc95ffefa185ce3d407a37f)" (is "?z_hcl")
    by (rule zenon_all_in_0 [of "chosen" "(\<lambda>x. (x \\in h7f4dc7fdc95ffefa185ce3d407a37f))", OF z_Hcg z_Hcf])
    have z_Hcm: "((CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {})))) \\in ?z_hbz)" (is "?z_hcm")
    by (rule subst [where P="(\<lambda>zenon_Voc. ((CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {})))) \\in zenon_Voc))", OF z_Hby z_Hcl])
    show FALSE
    proof (rule zenon_in_addElt [of "(CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {}))))" "?z_hca" "{}", OF z_Hcm])
     assume z_Hcq:"((CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {}))))=?z_hca)" (is "?z_hbs=_")
     show FALSE
     proof (rule notE [OF z_Hbf])
      have z_Hcr: "(?z_hbs=?z_hv)"
      proof (rule zenon_nnpp [of "(?z_hbs=?z_hv)"])
       assume z_Hcs:"(?z_hbs~=?z_hv)"
       show FALSE
       proof (rule notE [OF z_Hcs])
        have z_Hct: "(?z_hca=?z_hv)"
        by (rule sym [OF z_Hck])
        have z_Hcr: "(?z_hbs=?z_hv)"
        by (rule subst [where P="(\<lambda>zenon_Vtd. (?z_hbs=zenon_Vtd))", OF z_Hct], fact z_Hcq)
        thus "(?z_hbs=?z_hv)" .
       qed
      qed
      have z_Hu: "?z_hu"
      by (rule subst [where P="(\<lambda>zenon_Vxa. (zenon_Vxa \\in chosen))", OF z_Hcr], fact z_Hcf)
      thus "?z_hu" .
     qed
    next
     assume z_Hda:"((CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {})))) \\in {})" (is "?z_hda")
     show FALSE
     by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {}))))", OF z_Hda])
    qed
   next
    assume z_Hdb:"((CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen)))) \\in {})" (is "?z_hdb")
    show FALSE
    by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vx:(~((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))", OF z_Hdb])
   qed
  qed
 qed
 have zenon_L5_: "(h7f4dc7fdc95ffefa185ce3d407a37f={(CHOOSE x:((x \\in Value)&(h7f4dc7fdc95ffefa185ce3d407a37f={x})))}) ==> ((CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {})))) \\in chosen) ==> bAll(chosen, (\<lambda>x. (x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) ==> (\\A x:((x \\in chosen)=>(x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) ==> FALSE" (is "?z_hby ==> ?z_hcf ==> ?z_hcg ==> ?z_hb ==> FALSE")
 proof -
  assume z_Hby:"?z_hby" (is "_=?z_hbz")
  assume z_Hcf:"?z_hcf"
  assume z_Hcg:"?z_hcg"
  assume z_Hb:"?z_hb" (is "\\A x : ?z_hbd(x)")
  have z_Hbg: "(~(\\A zenon_Vx:((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))" (is "~(\\A x : ?z_hbi(x))")
  by (rule zenon_notsetequal_0 [of "h7f4dc7fdc95ffefa185ce3d407a37f" "chosen", OF z_Hbj])
  show FALSE
  by (rule zenon_L4_ [OF z_Hbg z_Hby z_Hcf z_Hcg z_Hb])
 qed
 assume z_Hf:"(~(((chosen={})&?z_hk)|(h7f4dc7fdc95ffefa185ce3d407a37f=chosen)))" (is "~(?z_hdd|?z_hdf)")
 have z_Hcg_z_Hd: "bAll(chosen, (\<lambda>x. (x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) == ?z_hd" (is "?z_hcg == _")
 by (unfold subset_def)
 have z_Hcg: "?z_hcg"
 by (unfold z_Hcg_z_Hd, fact z_Hd)
 have z_Hb_z_Hcg: "(\\A x:((x \\in chosen)=>(x \\in h7f4dc7fdc95ffefa185ce3d407a37f))) == ?z_hcg" (is "?z_hb == _")
 by (unfold bAll_def)
 have z_Hb: "?z_hb" (is "\\A x : ?z_hbd(x)")
 by (unfold z_Hb_z_Hcg, fact z_Hcg)
 have z_Hdg: "(~?z_hdd)" (is "~(?z_hde&_)")
 by (rule zenon_notor_0 [OF z_Hf])
 show FALSE
 proof (rule zenon_notand [OF z_Hdg])
  assume z_Hdh:"(chosen~={})"
  show FALSE
  proof (rule zenon_or [OF z_He])
   assume z_Hi:"?z_hi"
   show FALSE
   by (rule zenon_L2_ [OF z_Hi z_Hb])
  next
   assume z_Hk:"?z_hk"
   have z_Hdi_z_Hk: "(\\E x:((x \\in Value)&(h7f4dc7fdc95ffefa185ce3d407a37f={x}))) == ?z_hk" (is "?z_hdi == _")
   by (unfold bEx_def)
   have z_Hdi: "?z_hdi" (is "\\E x : ?z_hdj(x)")
   by (unfold z_Hdi_z_Hk, fact z_Hk)
   have z_Hdk: "?z_hdj((CHOOSE x:((x \\in Value)&(h7f4dc7fdc95ffefa185ce3d407a37f={x}))))" (is "?z_hdl&?z_hby")
   by (rule zenon_ex_choose_0 [of "?z_hdj", OF z_Hdi])
   have z_Hby: "?z_hby" (is "_=?z_hbz")
   by (rule zenon_and_1 [OF z_Hdk])
   have z_Hdm: "(~(\\A zenon_Vtb:((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {}))))" (is "~(\\A x : ?z_hdo(x))")
   by (rule zenon_notsetequal_0 [of "chosen" "{}", OF z_Hdh])
   have z_Hdp: "(\\E zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {}))))" (is "\\E x : ?z_hdq(x)")
   by (rule zenon_notallex_0 [of "?z_hdo", OF z_Hdm])
   have z_Hdr: "?z_hdq((CHOOSE zenon_Vtb:(~((zenon_Vtb \\in chosen)<=>(zenon_Vtb \\in {})))))" (is "~(?z_hcf<=>?z_hbr)")
   by (rule zenon_ex_choose_0 [of "?z_hdq", OF z_Hdp])
   show FALSE
   proof (rule zenon_notequiv [OF z_Hdr])
    assume z_Hds:"(~?z_hcf)"
    assume z_Hbr:"?z_hbr"
    show FALSE
    by (rule zenon_L3_ [OF z_Hbr])
   next
    assume z_Hcf:"?z_hcf"
    assume z_Hdt:"(~?z_hbr)"
    have z_Hbg: "(~(\\A zenon_Vx:((zenon_Vx \\in h7f4dc7fdc95ffefa185ce3d407a37f)<=>(zenon_Vx \\in chosen))))" (is "~(\\A x : ?z_hbi(x))")
    by (rule zenon_notsetequal_0 [of "h7f4dc7fdc95ffefa185ce3d407a37f" "chosen", OF z_Hbj])
    show FALSE
    by (rule zenon_L4_ [OF z_Hbg z_Hby z_Hcf z_Hcg z_Hb])
   qed
  qed
 next
  assume z_Hdu:"(~?z_hk)"
  show FALSE
  proof (rule zenon_or [OF z_He])
   assume z_Hi:"?z_hi"
   show FALSE
   by (rule zenon_L2_ [OF z_Hi z_Hb])
  next
   assume z_Hk:"?z_hk"
   show FALSE
   by (rule notE [OF z_Hdu z_Hk])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 123"; *} qed
end
