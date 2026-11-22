(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/SmallAngles.lean        *)
(* (N12Compact.Completion.OtherCases.C976LeftTop).  Section 3: the small    *)
(* left-angle interval uses only the actual marker, high point and real top *)
(* wall.  Squares N, W are cN sN uN vN aN, cW sW uW vW aW (OpenSquare        *)
(* invariants explicit); LeftInput c976lti_left; TopInput / QuadrantData /  *)
(* alpha / gamma (= beta) oltstsu_*; coefficients / upper_wall_normal       *)
(* C976LTI_*; lower_support_strict / target_low / target c976lttf_ /        *)
(* C976LTTF_*; ShallowTop.top_wall_faces OLTSTSU_TOP_WALL_FACES;            *)
(* wall_bounds OLTSTE_WALL_BOUNDS; CanonicalProjection.before CCCP_BEFORE;  *)
(* strict_bounds / ownU ABT_*.  Tag C976LTSA_.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_TopFaces.ml";;

let C976LTSA_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C976LTSA_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C976LTSA_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

(* Lean: small_residual (private) *)
let C976LTSA_SMALL_RESIDUAL = prove
 (`forall l h C S. &0 < l /\ &0 < h /\ l pow 2 + h pow 2 = &1 /\ (&21 / &65) * l < h /\
             h <= l / &3 /\ &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\
             C <= (&2 / &3) * S
     ==> &0 < C + S - &1 + S pow 2 * ((&2 / &5) * l * h - (&13 / &20) * h pow 2) -
              C * S * (&61 / &100 + (&2 / &5) * h pow 2 + (&13 / &20) * l * h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] OLTSTE_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`S:real`; `C:real`; `&4 / &5`; `&3 / &5`; `&1`; `&1`] CCCP_BEFORE) THEN
  ANTS_TAC THENL
  [CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[]; C976LTSA_LP_TAC];
   DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C976LTSA_PROD `&0 <= (l - &3 * h) * (l + &3 * h)` THEN
  SUBGOAL_THEN `h * h <= &1 / &10 /\ &9 / &10 <= l * l` STRIP_ASSUME_TAC THENL
  [C976LTSA_LP_TAC; ALL_TAC] THEN
  C976LTSA_PROD `&0 <= (l - &3 * h) * (&3 * l - h)` THEN
  SUBGOAL_THEN `l * h <= &3 / &10` ASSUME_TAC THENL [C976LTSA_LP_TAC; ALL_TAC] THEN
  C976LTSA_PROD `&0 < l * (h - (&8 / &25) * l)` THEN
  C976LTSA_PROD `&0 <= h * (l - &3 * h)` THEN
  SUBGOAL_THEN `&1 / &20 < (&2 / &5) * l * h - (&13 / &20) * h * h` ASSUME_TAC THENL
  [C976LTSA_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&61 / &100 + (&2 / &5) * h * h + (&13 / &20) * l * h <= &169 / &200`
    ASSUME_TAC THENL [C976LTSA_LP_TAC; ALL_TAC] THEN
  C976LTSA_PROD `&0 <= C * S` THEN
  SUBGOAL_THEN `&1 <= C + S` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C976LTSA_PROD `&0 <= (C + S) * (&1 - (C + S))` THEN C976LTSA_LP_TAC; ALL_TAC] THEN
  C976LTSA_PROD `&0 <= (&7 / &5 - (C + S)) * ((C + S) - &1)` THEN
  SUBGOAL_THEN `(&5 / &6) * C * S <= C + S - &1` ASSUME_TAC THENL
  [C976LTSA_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * S <= &1 / &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `C - S:real`]; ALL_TAC] THEN
  C976LTSA_PROD `&0 <= (S - &4 / &5) * (S + &4 / &5)` THEN
  SUBGOAL_THEN `&0 <= S * S` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  C976LTSA_PROD `&0 <= (S * S) * (((&2 / &5) * l * h - (&13 / &20) * h * h) - &1 / &20)` THEN
  C976LTSA_PROD `&0 <= (C * S) *
     (&169 / &200 - (&61 / &100 + (&2 / &5) * h * h + (&13 / &20) * l * h))` THEN
  C976LTSA_LP_TAC);;

(* Lean: small_impossible *)
let C976LTSA_SMALL_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c976lti_left cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     oltstsu_quadrant cW sW /\ aN = aW /\ sN <= cN / &3 /\
     cW - (&63 / &50) * sW <= vW /\
     (ABT_upper cN sN uN vN aN cN sN <= ABT_lower cW sW uW vW aW cN sN \/
      ABT_upper cN sN uN vN aN cW sW <= ABT_lower cW sW uW vW aW cW sW)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPEC_ALL C976LTTF_LOWER_SUPPORT_STRICT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = aW`)) THEN
  C976LTTF_SETUP_TAC `aW:real` THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
  [MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`; `cW:real`; `sW:real`]
     C976LTTF_TARGET_LOW) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`; `&13 / &20`; `&7 / &20`;
                 `cN:real`; `sN:real`] ABT_STRICT_BOUNDS) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   C976LTSA_PROD `&0 <= sW * (ABT_lower cW sW uW vW aW cN sN - ABT_upper cN sN uN vN aW cN sN)` THEN
   C976LTSA_PROD `&0 < sW * (ABT_upper cN sN uN vN aW cN sN - ((&13 / &50) * cN + sN))` THEN
   C976LTSA_LP_TAC;
   MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] OLTSTSU_TOP_WALL_FACES) THEN
   MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`; `cW:real`; `sW:real`]
     C976LTI_UPPER_WALL_NORMAL) THEN
   MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_OWNU) THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside; REAL_MUL_RID] THEN STRIP_TAC)
    [`linside cN sN uN vN aW (&13 / &20) (&7 / &20)`; `linside cN sN uN vN aW (&1 / &4) (&1)`] THEN
   C976LTSA_PROD `&0 < oltstsu_alpha cN sN cW sW *
                       ((uN + aW) - (cN * &13 / &20 + sN * &7 / &20))` THEN
   C976LTSA_PROD `&0 < oltstsu_gamma cN sN cW sW * ((vN + aW) - (--sN * &1 / &4 + cN))` THEN
   SUBGOAL_THEN
    `oltstsu_alpha cN sN cW sW * ((&13 / &20) * cN + (&7 / &20) * sN) +
     oltstsu_gamma cN sN cW sW * (cN - (&1 / &4) * sN) < ABT_upper cN sN uN vN aW cW sW`
    ASSUME_TAC THENL [C976LTSA_LP_TAC; ALL_TAC] THEN
   UNDISCH_TAC `ABT_upper cN sN uN vN aW cW sW <= ABT_lower cW sW uW vW aW cW sW` THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   C976LTSA_PROD `&0 < sW * (ABT_upper cN sN uN vN aW cW sW -
     (oltstsu_alpha cN sN cW sW * ((&13 / &20) * cN + (&7 / &20) * sN) +
      oltstsu_gamma cN sN cW sW * (cN - (&1 / &4) * sN)))` THEN
   C976LTSA_PROD `&0 <= sW * (uW - ABT_upper cN sN uN vN aW cW sW)` THEN
   C976LTSA_PROD `&0 <= cW * (vW - (cW - (&63 / &50) * sW))` THEN
   C976LTSA_PROD `&0 < (aW - &1) * (cW + sW)` THEN
   MP_TAC(SPECL [`cN:real`; `sN:real`; `cW:real`; `sW:real`] C976LTSA_SMALL_RESIDUAL) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN
    `sW * (oltstsu_alpha cN sN cW sW * ((&13 / &20) * cN + (&7 / &20) * sN) +
           oltstsu_gamma cN sN cW sW * (cN - (&1 / &4) * sN)) +
     cW pow 2 - (&63 / &50) * cW * sW + cW + sW - &2 =
     cW + sW - &1 + sW pow 2 * ((&2 / &5) * cN * sN - (&13 / &20) * sN pow 2) -
     cW * sW * (&61 / &100 + (&2 / &5) * sN pow 2 + (&13 / &20) * cN * sN)` ASSUME_TAC THENL
   [REWRITE_TAC[oltstsu_alpha; oltstsu_gamma] THEN
    MAP_EVERY UNDISCH_TAC [`cN pow 2 + sN pow 2 = &1`; `cW pow 2 + sW pow 2 = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C976LTSA_LP_TAC]);;
