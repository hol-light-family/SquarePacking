(* ========================================================================= *)
(* Port of Compact/Geometry/WallForcedPoint.lean                             *)
(* (with S12.short_projections from source/S12/ShortCluster/Projections).    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: S12.short_projections *)
let WFP_SHORT_PROJECTIONS = prove
 (`forall c s dx dy. c * c + s * s = &1 /\ dx pow 2 + dy pow 2 <= &1
     ==> --(&1) <= c * dx + s * dy /\ c * dx + s * dy <= &1 /\
         --(&1) <= --s * dx + c * dy /\ --s * dx + c * dy <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c * dx + s * dy) pow 2 + (--s * dx + c * dy) pow 2 <= &1` MP_TAC THENL
   [SUBGOAL_THEN `(c * dx + s * dy) pow 2 + (--s * dx + c * dy) pow 2 =
                  (c * c + s * s) * (dx pow 2 + dy pow 2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_LID]]; ALL_TAC] THEN
  SPEC_TAC(`--s * dx + c * dy`,`q:real`) THEN
  SPEC_TAC(`c * dx + s * dy`,`p:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  NLIN_TAC [SQ_NONNEG `p:real`; SQ_NONNEG `q:real`]);;

let WFP_SP tx ty =
  let th = SPECL [`c:real`; `s:real`; tx; ty] WFP_SHORT_PROJECTIONS in
  let th = CONV_RULE (LAND_CONV (RAND_CONV REAL_RAT_REDUCE_CONV)) th in
  REWRITE_RULE[] th;;

(* Lean: left_positive_point *)
let WFP_LEFT_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\
     &0 <= c * u - s * (v + a) /\
     lclosed c s u v a (&457 / &500) (&2) /\
     lclosed c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&19 / &25) (&187 / &100)) /\
     ~(linside c s u v a (&87 / &50) (&2))
     ==> linside c s u v a (&1) (&5 / &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside; lclosed] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `c - s:real`]
    [`s <= &1`; `&1 <= c + s`; `c + s <= &3 / &2`] THEN
  NLIN_FACTS_TAC []
    [`&1 + (&4 / &5) * c * s <= c + s`] THEN
  MP_TAC(WFP_SP `&6 / &25` `&63 / &100`) THEN
  MP_TAC(WFP_SP `&49 / &50` `&13 / &100`) THEN
  MP_TAC(WFP_SP `--(&37 / &50)` `&1 / &2`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `u + a <= c * &87 / &50 + s * &2 \/ --s * &87 / &50 + c * &2 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--s * &19 / &25 + c * &187 / &100 < v + a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &19 / &25 + s * &187 / &100 <= u \/ --s * &19 / &25 + c * &187 / &100 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_TAC [SQ_NONNEG `s:real`]]);;
