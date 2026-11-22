(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/LargeSupports.lean      *)
(* (N12Compact.Completion.OtherCases.C976LeftTop; Lean header: "Source      *)
(* translation only; these proofs are uncompiled").  Sections 5--6 of        *)
(* C976-LEFT-TOP-ANGLE: the support of the excluded segment is joined to     *)
(* both physical separating axes.  Squares N = cN sN uN vN aN and            *)
(* W = cW sW uW vW aW (OpenSquare invariants explicit); LeftInput            *)
(* c976lti_left; TopInput / QuadrantData oltstsu_top / oltstsu_quadrant;     *)
(* alpha / beta (= ShallowTop.alpha / gamma) oltstsu_alpha / oltstsu_gamma;  *)
(* Scalars.a0 / b0 / k0 / Elo / Ehi c976lts_*; lower_support_strict,         *)
(* target_low / target_high C976LTTF_*; upperU_strict / segment_support      *)
(* C976LTSG_*; coefficients / upper_wall_normal / width / angle_upper        *)
(* C976LTI_*; Scalars.left_low_margin / left_high_margin C976LTM_*;          *)
(* Scalars.lo_positive / hi_positive C976LTS_*; ShallowTop.top_wall_faces    *)
(* OLTSTSU_TOP_WALL_FACES; ownU ABT_OWNU.  Tag C976LTLS_.                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_TopFaces.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Segment.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Margins.ml";;

(* instantiate a lemma, prove its antecedent from the assumptions *)
let C976LTLS_USE th args =
  MP_TAC(SPECL args th) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
    DISCH_TAC];;

let C976LTLS_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aN:real = aW`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c976lti_left] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "c976lti_left" with _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[oltstsu_quadrant] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "oltstsu_quadrant" with _ -> false)) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aN:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c976lts_a0 cN sN` ASSUME_TAC THENL
   [REWRITE_TAC[c976lts_a0] THEN RASM_ARITH_TAC; ALL_TAC];;

(* Lean: left_axis_impossible *)
let C976LTLS_LEFT_AXIS_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c976lti_left cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     oltstsu_quadrant cW sW /\ aN = aW /\ (&1 / &3) * cN <= sN /\
     cW - (&63 / &50) * sW <= vW /\
     ABT_upper cN sN uN vN aN cN sN <= ABT_lower cW sW uW vW aW cN sN
     ==> false`,
  C976LTLS_SETUP_TAC THEN
  C976LTLS_USE C976LTTF_LOWER_SUPPORT_STRICT
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
     `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aN:real`] THEN
  C976LTLS_USE C976LTSG_UPPERU_STRICT [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
  SUBGOAL_THEN `sW * ABT_upper cN sN uN vN aN cN sN <= sW * ABT_lower cW sW uW vW aN cN sN`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_upper cN sN uN vN aN cN sN = uN + aN`]) THEN
  ASM_CASES_TAC `sN <= cN / &2` THENL
   [C976LTLS_USE C976LTM_LEFT_LOW_MARGIN [`cN:real`; `sN:real`] THEN
    SUBGOAL_THEN
     `c976lts_a0 cN sN + c976lts_b0 cN sN * (&1 - cN) - &39 / &625 -
      c976lts_a0 cN sN * ((&13 / &50) * cN + sN) =
      (&37 / &100) * cN + (&11 / &100) * sN - &189 / &625 - (&169 / &5000) * cN pow 2 -
      (&39 / &625) * cN * sN` ASSUME_TAC THENL
     [REWRITE_TAC[c976lts_a0; c976lts_b0] THEN UNDISCH_TAC `cN * cN + sN * sN = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `(&13 / &50) * cN + sN < uN + aN` ASSUME_TAC THENL
     [MP_TAC(SPECL [`(&13 / &50) * cN + sN`; `uN + aN`; `c976lts_a0 cN sN`] REAL_LT_LMUL_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
      MAP_EVERY UNDISCH_TAC
       [`c976lts_a0 cN sN + c976lts_b0 cN sN * (&1 - cN) - &39 / &625 < c976lts_a0 cN sN * (uN + aN)`;
        `c976lts_a0 cN sN + c976lts_b0 cN sN * (&1 - cN) - &39 / &625 -
         c976lts_a0 cN sN * ((&13 / &50) * cN + sN) =
         (&37 / &100) * cN + (&11 / &100) * sN - &189 / &625 - (&169 / &5000) * cN pow 2 -
         (&39 / &625) * cN * sN`;
        `&0 < (&37 / &100) * cN + (&11 / &100) * sN - &189 / &625 - (&169 / &5000) * cN pow 2 -
              (&39 / &625) * cN * sN`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    C976LTLS_USE C976LTTF_TARGET_LOW
      [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`] THEN
    SUBGOAL_THEN `sW * ((&13 / &50) * cN + sN) < sW * (uN + aN)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`sW * ABT_lower cW sW uW vW aN cN sN < c976lttf_target cN sN cW sW`;
      `c976lttf_target cN sN cW sW <= sW * ((&13 / &50) * cN + sN)`;
      `sW * (uN + aN) <= sW * ABT_lower cW sW uW vW aN cN sN`] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE] o check (is_neg o concl)) THEN
    C976LTLS_USE C976LTI_ANGLE_UPPER [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
    C976LTLS_USE C976LTM_LEFT_HIGH_MARGIN [`cN:real`; `sN:real`] THEN
    SUBGOAL_THEN
     `c976lts_a0 cN sN + c976lts_b0 cN sN * (&1 - cN) - &39 / &625 -
      c976lts_a0 cN sN * ((&4 / &25) * cN + (&6 / &5) * sN) =
      (&37 / &100) * cN + (&11 / &100) * sN - &219 / &625 + (&17 / &625) * cN pow 2 -
      (&161 / &2500) * cN * sN` ASSUME_TAC THENL
     [REWRITE_TAC[c976lts_a0; c976lts_b0] THEN UNDISCH_TAC `cN * cN + sN * sN = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `(&4 / &25) * cN + (&6 / &5) * sN < uN + aN` ASSUME_TAC THENL
     [MP_TAC(SPECL [`(&4 / &25) * cN + (&6 / &5) * sN`; `uN + aN`; `c976lts_a0 cN sN`] REAL_LT_LMUL_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
      MAP_EVERY UNDISCH_TAC
       [`c976lts_a0 cN sN + c976lts_b0 cN sN * (&1 - cN) - &39 / &625 < c976lts_a0 cN sN * (uN + aN)`;
        `c976lts_a0 cN sN + c976lts_b0 cN sN * (&1 - cN) - &39 / &625 -
         c976lts_a0 cN sN * ((&4 / &25) * cN + (&6 / &5) * sN) =
         (&37 / &100) * cN + (&11 / &100) * sN - &219 / &625 + (&17 / &625) * cN pow 2 -
         (&161 / &2500) * cN * sN`;
        `&0 < (&37 / &100) * cN + (&11 / &100) * sN - &219 / &625 + (&17 / &625) * cN pow 2 -
              (&161 / &2500) * cN * sN`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    C976LTLS_USE C976LTTF_TARGET_HIGH
      [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`] THEN
    SUBGOAL_THEN `sW * ((&4 / &25) * cN + (&6 / &5) * sN) < sW * (uN + aN)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`sW * ABT_lower cW sW uW vW aN cN sN < c976lttf_target cN sN cW sW`;
      `c976lttf_target cN sN cW sW <= sW * ((&4 / &25) * cN + (&6 / &5) * sN)`;
      `sW * (uN + aN) <= sW * ABT_lower cW sW uW vW aN cN sN`] THEN
    REAL_ARITH_TAC]);;

(* Lean: top_axis_impossible *)
let C976LTLS_TOP_AXIS_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c976lti_left cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     oltstsu_quadrant cW sW /\ aN = aW /\ (&1 / &3) * cN <= sN /\
     cW - (&63 / &50) * sW <= vW /\
     ABT_upper cN sN uN vN aN cW sW <= ABT_lower cW sW uW vW aW cW sW
     ==> false`,
  C976LTLS_SETUP_TAC THEN
  C976LTLS_USE C976LTI_COEFFICIENTS
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
   `oltstsu_gamma cN sN cW sW * c976lts_a0 cN sN - oltstsu_alpha cN sN cW sW * c976lts_b0 cN sN =
    c976lts_k0 cW sW` ASSUME_TAC THENL
   [REWRITE_TAC[oltstsu_gamma; oltstsu_alpha; c976lts_a0; c976lts_b0; c976lts_k0] THEN
    UNDISCH_TAC `cN * cN + sN * sN = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C976LTLS_USE C976LTSG_SEGMENT_SUPPORT [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
  C976LTLS_USE C976LTI_UPPER_WALL_NORMAL
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`] THEN
  (* lowerSupport *)
  SUBGOAL_THEN
   `aN * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) * c976lts_a0 cN sN +
    c976lts_k0 cW sW * vN - (&39 / &625) * oltstsu_alpha cN sN cW sW <=
    c976lts_a0 cN sN * ABT_upper cN sN uN vN aN cW sW` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `oltstsu_alpha cN sN cW sW * --(&39 / &625) <=
      oltstsu_alpha cN sN cW sW * (c976lts_a0 cN sN * uN + c976lts_b0 cN sN * vN)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      UNDISCH_TAC `c976lts_a0 cN sN * uN + c976lts_b0 cN sN * vN >= --(&39 / &625)` THEN
      REWRITE_TAC[real_ge] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(oltstsu_gamma cN sN cW sW * c976lts_a0 cN sN - oltstsu_alpha cN sN cW sW * c976lts_b0 cN sN) * vN =
      c976lts_k0 cW sW * vN` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `ABT_upper cN sN uN vN aN cW sW`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  C976LTLS_USE OLTSTSU_TOP_WALL_FACES [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aN:real`] THEN
  UNDISCH_TAC `ABT_upper cN sN uN vN aN cW sW <= ABT_lower cW sW uW vW aN cW sW` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* physical *)
  SUBGOAL_THEN
   `sW * c976lts_a0 cN sN * ABT_upper cN sN uN vN aN cW sW +
    c976lts_a0 cN sN * (aN * (cW + sW) + cW pow 2 - (&63 / &50) * cW * sW - &2) <= &0`
   ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 <= c976lts_a0 cN sN * (&2 - (sW * (uW + aN) + cW * (vW + aN))) /\
      &0 <= (c976lts_a0 cN sN * cW) * (vW - (cW - (&63 / &50) * sW)) /\
      &0 <= (c976lts_a0 cN sN * sW) * (uW - ABT_upper cN sN uN vN aN cW sW)`
     MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC REAL_LE_MUL) THEN RASM_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* necessary *)
  SUBGOAL_THEN
   `sW * (aN * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) * c976lts_a0 cN sN +
          c976lts_k0 cW sW * vN - (&39 / &625) * oltstsu_alpha cN sN cW sW) +
    c976lts_a0 cN sN * (aN * (cW + sW) + cW pow 2 - (&63 / &50) * cW * sW - &2) <= &0`
   ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 <= sW * (c976lts_a0 cN sN * ABT_upper cN sN uN vN aN cW sW -
        (aN * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) * c976lts_a0 cN sN +
         c976lts_k0 cW sW * vN - (&39 / &625) * oltstsu_alpha cN sN cW sW))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `sW * c976lts_a0 cN sN * ABT_upper cN sN uN vN aN cW sW +
      c976lts_a0 cN sN * (aN * (cW + sW) + cW pow 2 - (&63 / &50) * cW * sW - &2) <= &0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* D *)
  SUBGOAL_THEN
   `&0 < c976lts_a0 cN sN * (sW * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) + cW + sW)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < sW * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  C976LTLS_USE C976LTI_WIDTH [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
  C976LTLS_USE C976LTI_ANGLE_UPPER [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
  ASM_CASES_TAC `&0 <= c976lts_k0 cW sW` THENL
   [C976LTLS_USE C976LTS_LO_POSITIVE [`cN:real`; `sN:real`; `cW:real`; `sW:real`] THEN
    SUBGOAL_THEN
     `&0 <= (sW * c976lts_k0 cW sW) * (vN - (--(&27 / &100) * sN - (&1 / &25) * cN)) /\
      &0 < (aN - &1) * (c976lts_a0 cN sN *
             (sW * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) + cW + sW))`
     MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; RASM_ARITH_TAC];
        MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sW * (aN * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) * c976lts_a0 cN sN +
            c976lts_k0 cW sW * vN - (&39 / &625) * oltstsu_alpha cN sN cW sW) +
      c976lts_a0 cN sN * (aN * (cW + sW) + cW pow 2 - (&63 / &50) * cW * sW - &2) =
      c976lts_Elo cN sN cW sW +
      (aN - &1) * (c976lts_a0 cN sN *
         (sW * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) + cW + sW)) +
      (sW * c976lts_k0 cW sW) * (vN - (--(&27 / &100) * sN - (&1 / &25) * cN))`
     MP_TAC THENL
     [REWRITE_TAC[c976lts_Elo; c976lts_alpha; c976lts_beta; c976lts_a0; c976lts_k0;
                  oltstsu_alpha; oltstsu_gamma] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`&0 < c976lts_Elo cN sN cW sW`;
      `sW * (aN * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) * c976lts_a0 cN sN +
             c976lts_k0 cW sW * vN - (&39 / &625) * oltstsu_alpha cN sN cW sW) +
       c976lts_a0 cN sN * (aN * (cW + sW) + cW pow 2 - (&63 / &50) * cW * sW - &2) <= &0`] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE] o check (is_neg o concl)) THEN
    C976LTLS_USE C976LTS_HI_POSITIVE [`cN:real`; `sN:real`; `cW:real`; `sW:real`] THEN
    SUBGOAL_THEN `sW * c976lts_k0 cW sW <= &0` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= sW * --k ==> sW * k <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (sW * --c976lts_k0 cW sW) * (cN - (vN + aN)) /\
      &0 < (aN - &1) * (c976lts_a0 cN sN *
             (sW * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) + cW + sW) -
             sW * c976lts_k0 cW sW)`
     MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; RASM_ARITH_TAC];
        MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sW * (aN * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) * c976lts_a0 cN sN +
            c976lts_k0 cW sW * vN - (&39 / &625) * oltstsu_alpha cN sN cW sW) +
      c976lts_a0 cN sN * (aN * (cW + sW) + cW pow 2 - (&63 / &50) * cW * sW - &2) =
      c976lts_Ehi cN sN cW sW +
      (aN - &1) * (c976lts_a0 cN sN *
         (sW * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) + cW + sW) -
         sW * c976lts_k0 cW sW) +
      (sW * --c976lts_k0 cW sW) * (cN - (vN + aN))`
     MP_TAC THENL
     [REWRITE_TAC[c976lts_Ehi; c976lts_alpha; c976lts_beta; c976lts_a0; c976lts_k0;
                  oltstsu_alpha; oltstsu_gamma] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`&0 < c976lts_Ehi cN sN cW sW`;
      `sW * (aN * (oltstsu_alpha cN sN cW sW + oltstsu_gamma cN sN cW sW) * c976lts_a0 cN sN +
             c976lts_k0 cW sW * vN - (&39 / &625) * oltstsu_alpha cN sN cW sW) +
       c976lts_a0 cN sN * (aN * (cW + sW) + cW pow 2 - (&63 / &50) * cW * sW - &2) <= &0`] THEN
    REAL_ARITH_TAC]);;
