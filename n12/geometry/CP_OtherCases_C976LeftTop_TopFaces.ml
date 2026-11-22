(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/TopFaces.lean           *)
(* (N12Compact.Completion.OtherCases.C976LeftTop).  Section 2: the literal  *)
(* omitted right point of W exits below W.  Squares N, W are                *)
(* cN sN uN vN aN, cW sW uW vW aW (OpenSquare invariants explicit);         *)
(* LeftInput c976lti_left; TopInput / QuadrantData / alpha / gamma (= beta) *)
(* oltstsu_top / oltstsu_quadrant / oltstsu_alpha / oltstsu_gamma;          *)
(* coefficients / lower_left_normal C976LTI_*; ShallowTop.top_wall_faces    *)
(* OLTSTSU_TOP_WALL_FACES; ShallowTopExitScalars.wall_bounds, cosine_lower, *)
(* upper_exit_residual, marker_projection, F, G: OLTSTE_* / oltste_f / g;   *)
(* CanonicalProjection.before CCCP_BEFORE; strict_bounds / ownU ABT_*.      *)
(* Tag C976LTTF_ / c976lttf_.                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Directions.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ShallowTopExitScalars.ml";;

let C976LTTF_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C976LTTF_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C976LTTF_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C976LTTF_SETUP_TAC aN =
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; aN; `cW:real`; `sW:real`]
    C976LTI_COEFFICIENTS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] OLTSTE_WALL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[oltstsu_quadrant] o
    check (fun th -> concl th = `oltstsu_quadrant cW sW`)) THEN
  SUBGOAL_THEN `cW pow 2 + sW pow 2 = &1 /\ cN pow 2 + sN pow 2 = &1` STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c976lti_left] o
    check (fun th -> concl th = list_mk_comb(`c976lti_left`,
             [`cN:real`; `sN:real`; `uN:real`; `vN:real`; aN])));;

(* Lean: top_lowerV *)
let C976LTTF_TOP_LOWERV = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c976lti_left cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     oltstsu_quadrant cW sW /\ aN = aW /\
     (ABT_upper cN sN uN vN aN cN sN <= ABT_lower cW sW uW vW aW cN sN \/
      ABT_upper cN sN uN vN aN cW sW <= ABT_lower cW sW uW vW aW cW sW)
     ==> cW - (&63 / &50) * sW <= vW`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = aW`)) THEN
  C976LTTF_SETUP_TAC `aW:real` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[oltstsu_top] o
    check (fun th -> concl th = `oltstsu_top cW sW uW vW aW`)) THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside; REAL_MUL_RID] THEN STRIP_TAC)
   [`linside cW sW uW vW aW (&1) (&1)`; `linside cW sW uW vW aW (&1) (&543 / &500)`] THEN
  SUBGOAL_THEN `(&63 / &50) * cW + sW < uW + aW` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `(&43 / &500) * sW < (&13 / &50) * cW` ASSUME_TAC THENL
   [C976LTTF_LP_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`cW:real`; `sW:real`] OLTSTE_COSINE_LOWER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`cN:real`; `sN:real`; `cW:real`; `sW:real`] OLTSTE_UPPER_EXIT_RESIDUAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C976LTI_LOWER_LEFT_NORMAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C976LTTF_PROD `&0 <= oltstsu_alpha cN sN cW sW * (((&63 / &50) * cW + sW) - (uW + aW))` THEN
    C976LTTF_PROD `&0 < oltstsu_gamma cN sN cW sW * ((vW + aW) - (--sW + cW))` THEN
    C976LTTF_PROD `&0 < (aW - &1) * oltstsu_alpha cN sN cW sW` THEN
    SUBGOAL_THEN
     `oltstsu_alpha cN sN cW sW * ((&63 / &50) * cW + sW - &1) -
      oltstsu_gamma cN sN cW sW * (cW - sW) =
      (&13 / &20) * cN + (&7 / &20) * sN + cN * oltste_f cW + sN * oltste_g cW sW`
      ASSUME_TAC THENL
    [REWRITE_TAC[oltstsu_alpha; oltstsu_gamma; oltste_f; oltste_g] THEN
     UNDISCH_TAC `cW pow 2 + sW pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`; `&13 / &20`; `&7 / &20`;
                  `cN:real`; `sN:real`] ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    C976LTTF_LP_TAC;
    MP_TAC(SPECL [`cW:real`; `sW:real`] OLTSTE_MARKER_PROJECTION) THEN
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`; `&13 / &20`; `&7 / &20`;
                  `cW:real`; `sW:real`] ABT_STRICT_BOUNDS) THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_OWNU) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `ABT_upper cN sN uN vN aW cW sW <= ABT_lower cW sW uW vW aW cW sW` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C976LTTF_LP_TAC];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside cW sW uW vW aW (&63 / &50) (&1)` THEN
  REWRITE_TAC[linside; REAL_MUL_RID; TAUT `(~p ==> false) <=> p`] THEN C976LTTF_LP_TAC);;

(* Lean: target (definition) *)
let c976lttf_target = new_definition
 `c976lttf_target (cN:real) (sN:real) (cW:real) (sW:real) =
    cN * (cW - &1 + sW * (&63 / &50 - cW)) + sN * sW * (&2 - sW)`;;

(* Lean: lower_support_strict *)
let C976LTTF_LOWER_SUPPORT_STRICT = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c976lti_left cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     oltstsu_quadrant cW sW /\ aN = aW /\ cW - (&63 / &50) * sW <= vW
     ==> sW * ABT_lower cW sW uW vW aW cN sN < c976lttf_target cN sN cW sW`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = aW`)) THEN
  C976LTTF_SETUP_TAC `aW:real` THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] OLTSTSU_TOP_WALL_FACES) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C976LTI_LOWER_LEFT_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  C976LTTF_PROD `&0 <= oltstsu_alpha cN sN cW sW *
                       (&2 - (sW * (uW + aW) + cW * (vW + aW)))` THEN
  C976LTTF_PROD `&0 <= cN * (vW - (cW - (&63 / &50) * sW))` THEN
  C976LTTF_PROD `&0 < oltstsu_alpha cN sN cW sW * sW` THEN
  C976LTTF_PROD `&0 < (aW - &1) * (oltstsu_alpha cN sN cW sW * sW + cN)` THEN
  SUBGOAL_THEN
   `c976lttf_target cN sN cW sW -
    sW * (oltstsu_alpha cN sN cW sW * uW - oltstsu_gamma cN sN cW sW * (vW + aW)) =
    oltstsu_alpha cN sN cW sW * (&2 - sW * (uW + aW) - cW * (vW + aW)) +
    cN * (vW - (cW - (&63 / &50) * sW)) +
    (aW - &1) * (oltstsu_alpha cN sN cW sW * sW + cN)` ASSUME_TAC THENL
  [REWRITE_TAC[c976lttf_target; oltstsu_alpha; oltstsu_gamma] THEN
   UNDISCH_TAC `cW pow 2 + sW pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C976LTTF_LP_TAC);;

(* Lean: target_low *)
let C976LTTF_TARGET_LOW = prove
 (`forall cN sN uN vN aN cW sW.
     cN * cN + sN * sN = &1 /\ cW * cW + sW * sW = &1 /\
     c976lti_left cN sN uN vN aN /\ oltstsu_quadrant cW sW /\ sN <= (&1 / &2) * cN
     ==> c976lttf_target cN sN cW sW <= sW * ((&13 / &50) * cN + sN)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976LTTF_SETUP_TAC `aN:real` THEN
  MP_TAC(SPECL [`sW:real`; `cW:real`; `&4 / &5`; `&3 / &5`; `&1 / &2`; `&1`] CCCP_BEFORE) THEN
  ANTS_TAC THENL
  [CONV_TAC REAL_RAT_REDUCE_CONV THEN
   CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[]; C976LTTF_LP_TAC]; DISCH_TAC] THEN
  C976LTTF_PROD `&0 <= sW * ((&1 / &2) * cN - sN)` THEN
  C976LTTF_PROD `&0 <= cN * (&1 - cW - sW / &2)` THEN
  SUBGOAL_THEN `sN * sW <= cN * (&1 - cW)` ASSUME_TAC THENL [C976LTTF_LP_TAC; ALL_TAC] THEN
  C976LTTF_PROD `&0 <= (&1 - sW) * (cN * (&1 - cW) - sN * sW)` THEN
  REWRITE_TAC[c976lttf_target] THEN C976LTTF_LP_TAC);;

(* Lean: target_high *)
let C976LTTF_TARGET_HIGH = prove
 (`forall cN sN uN vN aN cW sW.
     cN * cN + sN * sN = &1 /\ cW * cW + sW * sW = &1 /\
     c976lti_left cN sN uN vN aN /\ oltstsu_quadrant cW sW /\ (&1 / &2) * cN <= sN
     ==> c976lttf_target cN sN cW sW <= sW * ((&4 / &25) * cN + (&6 / &5) * sN)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976LTTF_SETUP_TAC `aN:real` THEN
  MP_TAC(SPECL [`sW:real`; `cW:real`; `&4 / &5`; `&3 / &5`; `&1 / &2`; `&1`] CCCP_BEFORE) THEN
  ANTS_TAC THENL
  [CONV_TAC REAL_RAT_REDUCE_CONV THEN
   CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[]; C976LTTF_LP_TAC]; DISCH_TAC] THEN
  C976LTTF_PROD `&0 <= (&1 - sW) * (cN * (&1 - cW - sW / &2))` THEN
  C976LTTF_PROD `&0 <= (sW * (sN - (&1 / &2) * cN)) * (sW - &4 / &5)` THEN
  REWRITE_TAC[c976lttf_target] THEN C976LTTF_LP_TAC);;
