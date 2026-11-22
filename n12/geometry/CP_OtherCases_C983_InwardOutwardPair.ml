(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/InwardOutwardPair.lean         *)
(* (N12Compact.Completion.OtherCases.C983).  The genuine inward/outward      *)
(* duplicate in the C983 central reduction.  Squares N E B C R W are         *)
(* (cN, sN, uN, vN, aN), ...; apart is ldisj; pullY is LINSIDE_PULLY.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_CommonCases_OutwardPoint.ml";;

(* Lean: inward_outward_impossible *)
let C983IOP_INWARD_OUTWARD_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cE sE uE vE aE cB sB uB vB aB cC sC uC vC aC
    cR sR uR vR aR cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ cE * cE + sE * sE = &1 /\ cB * cB + sB * sB = &1 /\
     cC * cC + sC * sC = &1 /\ cR * cR + sR * sR = &1 /\ cW * cW + sW * sW = &1 /\
     &0 < aE /\ &0 < aB /\ &0 < aC /\ &0 < aR /\ &0 < aW /\
     &1 < aN /\ aN = aE /\
     linside cN sN uN vN aN (&47 / &20) (&47 / &20) /\
     linside cN sN uN vN aN (&2) (&113 / &50) /\
     linside cN sN uN vN aN (&113 / &50) (&2) /\
     ~linside cN sN uN vN aN (&12 / &5) (&3) /\
     linside cE sE uE vE aE (&47 / &20) (&33 / &20) /\
     linside cE sE uE vE aE (&3) (&87 / &50) /\
     linside cE sE uE vE aE (&3) (&8 / &5) /\
     linside cW sW uW vW aW (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cC sC uC vC aC (&3) (&1) /\ linside cC sC uC vC aC (&1543 / &500) (&1) /\
     (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> linside cB sB uB vB aB z (&1)) /\
     ldisj cN sN uN vN aN cE sE uE vE aE /\
     ldisj cN sN uN vN aN cW sW uW vW aW /\
     ldisj cE sE uE vE aE cR sR uR vR aR /\
     ldisj cE sE uE vE aE cC sC uC vC aC /\
     ldisj cE sE uE vE aE cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aN:real = aE` o concl)) THEN
  let sqN = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`]
  and sqE = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aN:real`] in
  let apart p q = list_mk_comb(`ldisj`, p @ q) in
  let no p q (x,y) known =
    ASSUME_TAC(REWRITE_RULE[ASSUME known]
      (SPECL [x; y] (REWRITE_RULE[ldisj] (ASSUME (apart p q))))) in
  let sq x = map (fun n -> mk_var(n^x,`:real`)) ["c";"s";"u";"v";"a"] in
  no sqN sqE (`&47 / &20`,`&33 / &20`) `linside cE sE uE vE aN (&47 / &20) (&33 / &20)` THEN
  no sqN (sq "W") (`&33 / &20`,`&47 / &20`) `linside cW sW uW vW aW (&33 / &20) (&47 / &20)` THEN
  no sqN sqE (`&113 / &50`,`&2`) `linside cN sN uN vN aN (&113 / &50) (&2)` THEN
  no sqE (sq "R") (`&1543 / &500`,`&2`) `linside cR sR uR vR aR (&1543 / &500) (&2)` THEN
  no sqE (sq "C") (`&3`,`&1`) `linside cC sC uC vC aC (&3) (&1)` THEN
  no sqE (sq "C") (`&1543 / &500`,`&1`) `linside cC sC uC vC aC (&1543 / &500) (&1)` THEN
  SUBGOAL_THEN `forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside cE sE uE vE aN z (&1)`
    ASSUME_TAC THENL
   [X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(MP (MP (SPEC `z:real` (ASSUME
      `forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> linside cB sB uB vB aB z (&1)`))
      (ASSUME `&113 / &50 <= z`)) (ASSUME `z <= &14 / &5`)) THEN
    MP_TAC(SPECL [`z:real`; `&1`] (REWRITE_RULE[ldisj] (ASSUME (apart sqE (sq "B"))))) THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `linside cN sN uN vN aN (&123 / &50) (&201 / &100)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `&201 / &100 = &4 - &199 / &100`] THEN
    REWRITE_TAC[GSYM LINSIDE_PULLY] THEN MATCH_MP_TAC CCIP_POINT_ORIGINAL THEN
    REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) then FIRST_ASSUM ACCEPT_TAC g else ASM_REAL_ARITH_TAC g);
    ALL_TAC] THEN
  SUBGOAL_THEN `linside cE sE uE vE aN (&123 / &50) (&201 / &100)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `&201 / &100 = &4 - &199 / &100`] THEN
    REWRITE_TAC[GSYM LINSIDE_PULLY] THEN MATCH_MP_TAC CCOP_POINT_ORIGINAL THEN
    REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) then FIRST_ASSUM ACCEPT_TAC g else ASM_REAL_ARITH_TAC g);
    ALL_TAC] THEN
  MP_TAC(SPECL [`&123 / &50`; `&201 / &100`] (REWRITE_RULE[ldisj] (ASSUME (apart sqN sqE)))) THEN
  ASM_REWRITE_TAC[]);;
