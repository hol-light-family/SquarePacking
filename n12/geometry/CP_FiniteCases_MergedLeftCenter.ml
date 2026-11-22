(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/MergedLeftCenter.lean              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/MergedLeftEscapeAux.ml";;
needs "n12/geometry/MergedLeftNegative.ml";;

(* Lean: point *)
let FCMLC_POINT = prove
 (`forall cA sA uA vA aA cL sL uL vL aL.
     cA * cA + sA * sA = &1 /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aA /\ aA = aL /\ lcont cL sL uL vL aL /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1) (&87 / &50) /\
     ~linside cA sA uA vA aA (&1) (&113 / &50) /\
     ~linside cA sA uA vA aA (&2) (&87 / &50) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\
     ~linside cA sA uA vA aA (&8 / &5) (&3) /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cL sL uL vL aL (&1) (&12 / &5) /\
     ldisj cA sA uA vA aA cL sL uL vL aL
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aL` o concl)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aq:real = aA` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sq` THENL
   [ASM_CASES_TAC `linside cq sq uq vq aA (&2) (&2)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aA:real`] MLEA_INWARD) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MLN_POINT THEN
    MAP_EVERY EXISTS_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aA:real`] THEN
    ASM_REWRITE_TAC[ldisj] THEN ASM_REAL_ARITH_TAC]);;
