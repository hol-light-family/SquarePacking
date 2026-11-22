(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976NegativeTop/LeftFace.lean       *)
(* (N12Compact.Completion.OtherCases.C976NegativeTop).  Section 2: the       *)
(* genuine left point omitted by the top square forces its lower-U face;     *)
(* both signs of the relative-axis coefficient are kept.                     *)
(* Lean's N with N.s = -s is (c, s, u, v, a) with s = --t; W is              *)
(* (cW, sW, uW, vW, aW).  Faces: cc976f_faces; upper / lower: ABT_upper /    *)
(* ABT_lower; ownU / ownV: ABT_OWNU / ABT_OWNV; quadrant_bounds /            *)
(* lower_exit_margin: C976NTQ_*; WallProfile.downward_upper /                *)
(* upper_in_bands: OCWPSG_DOWNWARD_UPPER / OCWPSG_UPPER_IN_BANDS.            *)
(* Tag CC976LF_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_SeparatingAxes.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_QuadrantScalars.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;

let CC976LF_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   RASM_ARITH_TAC; ALL_TAC];;

(* Lean: left_face *)
let CC976LF_LEFT_FACE = prove
 (`forall c s u v a cW sW uW vW aW t.
     c * c + s * s = &1 /\ &0 < a /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     s = --t /\ &1 < a /\ a = aW /\ &0 < c /\ &0 < t /\ t <= c /\
     &0 < cW /\ &0 <= sW /\ (&2 / &3) * sW <= cW /\
     cc976f_faces c s u v a t /\
     linside cW sW uW vW aW (&0) (&0) /\
     ~linside cW sW uW vW aW (--(&18 / &25)) (&0) /\
     (ABT_upper cW sW uW vW aW c s <= ABT_lower c s u v a c s \/
      ABT_upper c s u v a (--sW) cW <= ABT_lower cW sW uW vW aW (--sW) cW)
     ==> --(&18 / &25) * cW <= uW`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:real = aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `cc976f_faces c s u v a t`) (concl th)
    then MAP_EVERY ASSUME_TAC (CONJUNCTS (REWRITE_RULE[cc976f_faces] th)) else NO_TAC) THEN
  SUBGOAL_THEN `uW < &0 /\ &0 < uW + a /\ vW < &0 /\ &0 < vW + a` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cW sW uW vW a (&0) (&0)` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] C976NTQ_QUADRANT_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c * c + t * t = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `t:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * sW + t * cW` ASSUME_TAC THENL
   [CC976LF_PROD `&0 <= c * sW` THEN CC976LF_PROD `&0 < t * cW` THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c * cW - t * sW) * (c * cW - t * sW) + (c * sW + t * cW) * (c * sW + t * cW) = &1`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + t * t = &1` THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  ABBREV_TAC `d = c * cW - t * sW` THEN
  ABBREV_TAC `k = c * sW + t * cW` THEN
  SUBGOAL_THEN `k <= &1` ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `d:real`]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `vW + a <= (&18 / &25) * sW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cW sW uW vW a (--(&18 / &25)) (&0)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vW < --(&1 - (&3 / &4) * sW)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cW sW uW vW a c (--t) = d * uW - k * vW + a * max d (&0)`
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `a:real`; `c:real`; `t:real`]
      OCWPSG_DOWNWARD_UPPER) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MAP_EVERY EXPAND_TAC ["d"; "k"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper c (--t) u v a (--sW) cW = --k * u + d * v + a * max d (&0)`
    ASSUME_TAC THENL
   [REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `--sW * c + cW * --t = --k /\ --(--sW) * --t + cW * c = d`
      (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY EXPAND_TAC ["d"; "k"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs(--k) = k`] THEN
    ASM_CASES_TAC `&0 <= d` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x /\ max x (&0) = x`;
                 REAL_ARITH `~(&0 <= x) ==> abs x = --x /\ max x (&0) = &0`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `a:real`] ABT_OWNV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC o check (fun th -> is_disj(concl th) &&
     can (find_term ((=) `ABT_upper`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [(* northAxis *)
    SUBGOAL_THEN `&0 <= d * uW + a * max d (&0)` ASSUME_TAC THENL
     [ASM_CASES_TAC `&0 <= d` THENL
       [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`] THEN
        CC976LF_PROD `&0 <= d * (uW + a)` THEN RASM_ARITH_TAC;
        ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> max x (&0) = &0`] THEN
        CC976LF_PROD `&0 <= --d * --uW` THEN RASM_ARITH_TAC]; ALL_TAC] THEN
    CC976LF_PROD `&0 < k * (--(&1 - (&3 / &4) * sW) - vW)` THEN
    SUBGOAL_THEN `k * (&1 - (&3 / &4) * sW) < u` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `t:real`; `cW:real`; `sW:real`] C976NTQ_LOWER_EXIT_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
    (* topAxis *)
    SUBGOAL_THEN `&0 <= d * v + a * max d (&0)` ASSUME_TAC THENL
     [ASM_CASES_TAC `&0 <= d` THENL
       [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`] THEN
        CC976LF_PROD `&0 <= d * (v + a)` THEN RASM_ARITH_TAC;
        ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> max x (&0) = &0`] THEN
        CC976LF_PROD `&0 <= --d * --v` THEN RASM_ARITH_TAC]; ALL_TAC] THEN
    CC976LF_PROD `&0 < k * ((&13 / &50) * c - u)` THEN
    SUBGOAL_THEN `--(&13 / &50) * c * k < vW` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    CC976LF_PROD `&0 <= (&1 - c) * k` THEN
    RASM_ARITH_TAC]);;
