(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShortWallCycle.lean                       *)
(* (N12Compact.C981CompletionShortWallCycle).  The shorter-wall common       *)
(* ending.  Squares a = (cA, sA, uA, vA, aA), b = (cB, sB, uB, vB, aB);      *)
(* apart is ldisj; pullY is LINSIDE_PULLY.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_ShortOutwardLock.ml";;
needs "n12/geometry/CP_CommonCases_ShortOutwardPoint.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;

(* Lean: impossible *)
let C981SWC_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aA /\ aA = aB /\
     linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&12 / &5) (&1) /\
     linside cB sB uB vB aB (&47 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&3) (&113 / &50) /\
     linside cB sB uB vB aB (&3) (&12 / &5) /\
     ~linside cB sB uB vB aB (&1543 / &500) (&2) /\
     ~linside cB sB uB vB aB (&113 / &50) (&3) /\
     ~linside cB sB uB vB aB (&273 / &100) (&3) /\
     ~linside cB sB uB vB aB (&3) (&3) /\
     ~linside cB sB uB vB aB (&1543 / &500) (&3) /\
     (forall z. &113 / &50 <= z ==> z <= &273 / &100 ==> ~linside cB sB uB vB aB z (&3)) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aB` o concl)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CCIP_STRONG_ORIGINAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `ldisj c s u v a c' s' u' v' a'`) (concl th)
    then MP_TAC(SPECL [`&127 / &50`; `&199 / &100`] (REWRITE_RULE[ldisj] th)) THEN
         MP_TAC(SPECL [`&113 / &50`; `&2`] (REWRITE_RULE[ldisj] th))
    else NO_TAC) THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aA:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = aA` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [SUBGOAL_THEN `linside cr sr ur vr aA (&127 / &50) (&199 / &100)` MP_TAC THENL
     [MATCH_MP_TAC CCSOP_POSITIVE_POINT_ORIGINAL THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN
      (fun g -> if is_neg(snd g) then ASM_MESON_TAC[] g else ASM_REAL_ARITH_TAC g);
      ASM_MESON_TAC[]];
    MATCH_MP_TAC C981SOL_NONNEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `--sr`; `ur - &4 * sr`; `&4 * cr - vr - aA`; `aA:real`] THEN
    REWRITE_TAC[LINSIDE_PULLY] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) || is_neg(snd g) then ASM_MESON_TAC[] g
             else ASM_REAL_ARITH_TAC g)]);;
