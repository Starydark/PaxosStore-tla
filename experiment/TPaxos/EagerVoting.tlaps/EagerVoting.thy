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

lemma ob'7:
(* usable definition PropositionalTemporalLogic suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition IsBijection suppressed *)
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
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!NatInductiveDefHypothesis suppressed *)
(* usable definition C!NatInductiveDefConclusion suppressed *)
(* usable definition C!FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition C!FiniteNatInductiveDefConclusion suppressed *)
(* usable definition C!IsBijection suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!Inv suppressed *)
assumes v'140: "((\<forall> Q \<in> (Quorum) : (((Q) \<subseteq> (Acceptor)))) & (\<forall> a_Q1a \<in> (Quorum) : (\<forall> a_Q2a \<in> (Quorum) : (((((a_Q1a) \<inter> (a_Q2a))) \<noteq> ({}))))))"
assumes v'141: "(\<forall>S : (\<forall>T : (((\<forall>x : (((((x) \<in> (S))) \<Leftrightarrow> (((x) \<in> (T)))))) \<Rightarrow> (((S) = (T)))))))"
shows "((((((votes) = ([ a \<in> (Acceptor)  \<mapsto> ({})]))) & (((maxBal) = ([ a \<in> (Acceptor)  \<mapsto> ((minus (((Succ[0])))))])))) \<Rightarrow> (((subsetOf((Value), %v. (\<exists> b \<in> (Ballot) : (\<exists> Q \<in> (Quorum) : (\<forall> a \<in> (Q) : (((<<(b), (v)>>) \<in> (fapply ((votes), (a)))))))))) = ({})))))"(is "PROP ?ob'7")
proof -
ML_command {* writeln "*** TLAPS ENTER 7"; *}
show "PROP ?ob'7"
using assms by force
ML_command {* writeln "*** TLAPS EXIT 7"; *} qed
lemma ob'15:
(* usable definition PropositionalTemporalLogic suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition IsBijection suppressed *)
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
(* usable definition C!IsFiniteSet suppressed *)
(* usable definition C!Cardinality suppressed *)
(* usable definition C!PropositionalTemporalLogic suppressed *)
(* usable definition C!NatInductiveDefHypothesis suppressed *)
(* usable definition C!NatInductiveDefConclusion suppressed *)
(* usable definition C!FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition C!FiniteNatInductiveDefConclusion suppressed *)
(* usable definition C!IsBijection suppressed *)
(* usable definition C!Init suppressed *)
(* usable definition C!Spec suppressed *)
(* usable definition C!Inv suppressed *)
assumes v'155: "(((a_hef12f5554781c2213604492856f635a :: c)) & ((a_h51861ad69648f81a4743d26221e064a :: c)) & (Next))"
assumes v'156: "(((chosen) \<subseteq> ((h7f4dc7fdc95ffefa185ce3d407a37f :: c))))"
assumes v'157: "((((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) = ({}))) \<or> (\<exists> v \<in> (Value) : ((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) = ({(v)}))))))"
shows "((((((chosen) = ({}))) & (\<exists> v \<in> (Value) : ((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) = ({(v)}))))) \<or> ((((h7f4dc7fdc95ffefa185ce3d407a37f :: c)) = (chosen)))))"(is "PROP ?ob'15")
proof -
ML_command {* writeln "*** TLAPS ENTER 15"; *}
show "PROP ?ob'15"

(* BEGIN ZENON INPUT
;; file=EagerVoting.tlaps/tlapm_65f2e7.znn; PATH="${PATH}:/usr/local/bin:/usr/local/lib/tlaps/bin"; zenon -p0 -x tla -oisar -max-time 1d "$file" >EagerVoting.tlaps/tlapm_65f2e7.znn.out
;; obligation #15
$hyp "v'155" (/\ a_hef12f5554781c2213604492856f635a
a_h51861ad69648f81a4743d26221e064a Next)
$hyp "v'156" (TLA.subseteq chosen
h7f4dc7fdc95ffefa185ce3d407a37f)
$hyp "v'157" (\/ (= h7f4dc7fdc95ffefa185ce3d407a37f TLA.emptyset)
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
 using v'156 by blast
 have z_He:"((h7f4dc7fdc95ffefa185ce3d407a37f={})|bEx(Value, (\<lambda>v. (h7f4dc7fdc95ffefa185ce3d407a37f={v}))))" (is "?z_hi|?z_hk")
 using v'157 by blast
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
ML_command {* writeln "*** TLAPS EXIT 15"; *} qed
end
