(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/Inputs.lean             *)
(* (namespace N12Compact.Completion.OtherCases.C976LeftTop).                *)
(* Literal local inputs of C976-LEFT-TOP-ANGLE Theorem 1.                   *)
(* TopInput / QuadrantData / alpha / beta are the ShallowTop ones:           *)
(* oltstsu_top, oltstsu_quadrant, oltstsu_alpha, oltstsu_gamma.            *)
(* lower / upper: ABT_lower / ABT_upper.  N = (c, s, u, v, a); the          *)
(* OpenSquare invariants are explicit hypotheses.                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ShallowTopSupport.ml";;
needs "n12/geometry/CP_OtherCases_LowerCornerSupport.ml";;

(* Lean: LeftInput (structure) *)
let c976lti_left = new_definition
 `c976lti_left (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\
    (&21 / &65) * c < s /\
    v + a <= c /\
    --(&27 / &100) * s - (&1 / &25) * c <= v /\
    linside c s u v a (&13 / &20) (&7 / &20) /\
    linside c s u v a (--(&43) / &500) (&0) /\
    linside c s u v a (&0) (&13 / &50) /\
    linside c s u v a (&1 / &4) (&1) /\
    (forall t. &0 <= t ==> t <= &1
         ==> ~linside c s u v a (--(&6) / &25 + (&6 / &25) * t)
                                (--(&13) / &100 - (&13 / &100) * t))`;;

(* Lean: coefficients *)
let C976LTI_COEFFICIENTS = prove
 (`forall cN sN uN vN aN cW sW.
     c976lti_left cN sN uN vN aN /\ oltstsu_quadrant cW sW
     ==> &0 < oltstsu_alpha cN sN cW sW /\ &0 < oltstsu_gamma cN sN cW sW`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c976lti_left; oltstsu_quadrant;
    oltstsu_alpha; oltstsu_gamma] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `cW:real`; `sW:real`]
    OLTSTD_RELATIVE_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: upper_wall_normal *)
let C976LTI_UPPER_WALL_NORMAL = prove
 (`forall cN sN uN vN aN cW sW.
     c976lti_left cN sN uN vN aN /\ oltstsu_quadrant cW sW
     ==> ABT_upper cN sN uN vN aN cW sW =
         oltstsu_alpha cN sN cW sW * (uN + aN) + oltstsu_gamma cN sN cW sW * (vN + aN)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`]
    C976LTI_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[oltstsu_alpha; oltstsu_gamma] THEN STRIP_TAC THEN
  REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `cW * cN + sW * sN = cN * cW + sN * sW /\
                --cW * sN + sW * cN = cN * sW - sN * cW` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN REAL_ARITH_TAC);;

(* Lean: lower_left_normal *)
let C976LTI_LOWER_LEFT_NORMAL = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c976lti_left cN sN uN vN aN /\ oltstsu_quadrant cW sW
     ==> ABT_lower cW sW uW vW aW cN sN =
         oltstsu_alpha cN sN cW sW * uW - oltstsu_gamma cN sN cW sW * (vW + aW)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`]
    C976LTI_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `cN:real`; `sN:real`;
                `oltstsu_alpha cN sN cW sW`; `--(oltstsu_gamma cN sN cW sW)`]
    C1092WS_LOWER_PN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[oltstsu_alpha; oltstsu_gamma] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[oltstsu_alpha; oltstsu_gamma]) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

(* Lean: width *)
let C976LTI_WIDTH = prove
 (`forall c s u v a. c976lti_left c s u v a ==> &1 < (&26 / &25) * c + (&27 / &100) * s`,
  REWRITE_TAC[c976lti_left] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: angle_upper *)
let C976LTI_ANGLE_UPPER = prove
 (`forall c s u v a. c * c + s * s = &1 /\ c976lti_left c s u v a ==> s < (&8 / &11) * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C976LTI_WIDTH) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&11 * c + &8 * s) pow 2 <= &185` ASSUME_TAC THENL
   [MP_TAC(SPEC `&8 * c - &11 * s` REAL_LE_POW_2) THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&26 / &25) * c + (&27 / &100) * s <= (&68 / &925) * (&11 * c + &8 * s)`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&68 / &925) * (&11 * c + &8 * s) < &1` ASSUME_TAC THENL
   [ABBREV_TAC `z = (&68 / &925) * (&11 * c + &8 * s)` THEN
    SUBGOAL_THEN `z pow 2 < &1` MP_TAC THENL
     [EXPAND_TAC "z" THEN UNDISCH_TAC `(&11 * c + &8 * s) pow 2 <= &185` THEN
      REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `z - &1` REAL_LE_POW_2) THEN REWRITE_TAC[REAL_POW_2] THEN
      DISCH_TAC THEN DISCH_TAC THEN NLIN_TAC []];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
