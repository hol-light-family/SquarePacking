(* ========================================================================= *)
(* Port of Compact/Geometry/WallLowerBarrier.lean                            *)
(* (short_projections: WFP_SHORT_PROJECTIONS, instantiated by WFP_SP).       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: left_positive_point *)
let WLB_LEFT_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\
     &0 <= c * u - s * (v + a) /\
     lclosed c s u v a (&457 / &500) (&2) /\
     lclosed c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&1) (&87 / &50)) /\
     ~(linside c s u v a (&87 / &50) (&2))
     ==> linside c s u v a (&1) (&5 / &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside; lclosed] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `c - s:real`]
    [`&1 <= c + s`; `c + s <= &3 / &2`] THEN
  NLIN_FACTS_TAC [] [`&1 + (&4 / &5) * c * s <= c + s`] THEN
  MP_TAC(WFP_SP `&0` `&19 / &25`) THEN
  MP_TAC(WFP_SP `&37 / &50` `&13 / &50`) THEN
  MP_TAC(WFP_SP `--(&37 / &50)` `&1 / &2`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `u + a <= c * &87 / &50 + s * &2 \/ --s * &87 / &50 + c * &2 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c + s * &87 / &50 < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`c <= &1`; `&1 <= c`] THEN
    SUBGOAL_THEN `c = &1` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &1 + s * &87 / &50 <= u \/ --s * &1 + c * &87 / &50 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_TAC [SQ_NONNEG `s:real`]]);;
