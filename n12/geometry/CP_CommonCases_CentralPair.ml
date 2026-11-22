(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/CentralPair.lean                   *)
(* (N12Compact.CommonCases.CentralPair).  The complete local                 *)
(* inward/mixed-or-outward ending.  Squares a = (cA, ..., aA) and            *)
(* n = (cN, ..., aN); apart is ldisj; pullY is LINSIDE_PULLY.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_CommonCases_OutwardPoint.ml";;
needs "n12/geometry/CP_C981_OutwardAnchor.ml";;

(* Lean: impossible *)
let CCCPAIR_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cN sN uN vN aN.
     cA * cA + sA * sA = &1 /\ cN * cN + sN * sN = &1 /\ &1 < aA /\ &1 < aN /\
     linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&12 / &5) (&1) /\
     linside cN sN uN vN aN (&47 / &20) (&47 / &20) /\
     ((linside cN sN uN vN aN (&2) (&113 / &50) /\ linside cN sN uN vN aN (&3) (&12 / &5)) \/
      (linside cN sN uN vN aN (&3) (&113 / &50) /\ linside cN sN uN vN aN (&3) (&12 / &5))) /\
     ~linside cN sN uN vN aN (&1543 / &500) (&2) /\
     ~linside cN sN uN vN aN (&3) (&3) /\
     ~linside cN sN uN vN aN (&1543 / &500) (&3) /\
     (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside cN sN uN vN aN z (&3)) /\
     ldisj cA sA uA vA aA cN sN uN vN aN
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `ldisj c s u v a c' s' u' v' a'`) (concl th)
    then MP_TAC(SPECL [`&47 / &20`; `&47 / &20`] (REWRITE_RULE[ldisj] th)) THEN
         MP_TAC(SPECL [`&113 / &50`; `&2`] (REWRITE_RULE[ldisj] th)) THEN
         MP_TAC(SPECL [`&123 / &50`; `&199 / &100`] (REWRITE_RULE[ldisj] th))
    else NO_TAC) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
                ~linside cN sN uN vN aN (&113 / &50) (&2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THENL
   [MATCH_MP_TAC C981OA_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cN:real`; `--sN`; `uN - &4 * sN`; `&4 * cN - vN - aN`; `aN:real`] THEN
    REWRITE_TAC[LINSIDE_PULLY] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) then ASM_MESON_TAC[] g else ASM_REAL_ARITH_TAC g);
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CCIP_POINT_ORIGINAL) THEN
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] CCOP_POINT_ORIGINAL) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
