(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/ShallowTopPair.lean *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTop). *)
(* The complete actual-square join in Theorem 2 of                          *)
(* ORDINARY-LEFT-TOP-OBSTRUCTION.                                           *)
(* OrdinaryData / TopInput / QuadrantData / alpha / gamma: oltstsu_* (Shallow*)
(* TopSupport); Input: ocolti_input; frame: OLTM_FRAME (profile oltp_profile);*)
(* longitudinal_alternatives: OLTSTD_LONGITUDINAL_ALTERNATIVES; strict_bounds:*)
(* ABT_STRICT_BOUNDS; ownU: ABT_OWNU; ShallowTopExitScalars: OLTSTE_* /     *)
(* oltste_f, oltste_g.  turnFrame (c, s, u, v, a) = (--s, c, v, --u - a, a). *)
(* N = (cN, sN, uN, vN, aN), W = (cW, sW, uW, vW, aW); the OpenSquare        *)
(* invariants are explicit hypotheses.                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_Main.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ShallowTopSupport.ml";;

(* Lean: quadrant_impossible *)
let OLTSTP_QUADRANT_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     oltstsu_ordinary cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     oltstsu_quadrant cW sW /\ aN = aW /\
     ldisj cN sN uN vN aN cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    OLTSTSU_LOWER_ORDINARY_NORMAL) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`]
    OLTSTSU_COEFFICIENTS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `&13 / &20`; `&7 / &20`; `cN:real`; `sN:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `&13 / &20`; `&7 / &20`; `cW:real`; `sW:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    OLTSTD_LONGITUDINAL_ALTERNATIVES) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[oltstsu_ordinary] o
    check (fun th -> fst(strip_comb(concl th)) = `oltstsu_ordinary`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[oltstsu_quadrant] o
    check (fun th -> fst(strip_comb(concl th)) = `oltstsu_quadrant`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[oltstsu_top] o
    check (fun th -> fst(strip_comb(concl th)) = `oltstsu_top`)) THEN
  SUBGOAL_THEN `cW pow 2 + sW pow 2 = &1 /\ cN pow 2 + sN pow 2 = &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[oltstsu_alpha; oltstsu_gamma] THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] OLTSTE_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(REWRITE_RULE[linside; REAL_MUL_RID] (ASSUME `linside cW sW uW vW aW (&1) (&1)`)) THEN
  MP_TAC(REWRITE_RULE[linside; REAL_MUL_RID] (ASSUME `linside cW sW uW vW aW (&1) (&543 / &500)`)) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(uW + aW <= (&63 / &50) * cW + sW)` ASSUME_TAC THENL
   [DISCH_TAC THEN
  SUBGOAL_THEN `(&43 / &500) * sW < (&13 / &50) * cW` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] OLTSTE_COSINE_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
    [MP_TAC(SPECL [`cN:real`; `sN:real`; `cW:real`; `sW:real`] OLTSTE_UPPER_EXIT_RESIDUAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(cN * cW + sN * sW) * (uW + aW) <= (cN * cW + sN * sW) * ((&63 / &50) * cW + sW) /\
    (cN * sW - sN * cW) * (--sW + cW) < (cN * sW - sN * cW) * (vW + aW) /\
    &0 < (aW - &1) * (cN * cW + sN * sW)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN RASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LMUL THEN RASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(cN * cW + sN * sW) * ((&63 / &50) * cW + sW - &1) - (cN * sW - sN * cW) * (cW - sW) =
    (&13 / &20) * cN + (&7 / &20) * sN + cN * oltste_f cW + sN * oltste_g cW sW`
    ASSUME_TAC THENL
   [REWRITE_TAC[oltste_f; oltste_g] THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  RASM_ARITH_TAC;
     MP_TAC(SPECL [`cW:real`; `sW:real`] OLTSTE_MARKER_PROJECTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `cW - (&63 / &50) * sW <= vW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cW sW uW vW aW (&63 / &50) (&1)` THEN
    REWRITE_TAC[linside; REAL_MUL_RID] THEN
    SUBGOAL_THEN `&0 <= cW * &63 / &50 - cW /\ &0 <= sW - sW * &63 / &50 + sW * &63 / &50 - sW`
      MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MATCH_MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
      OLTSTSU_ORDINARY_AXIS_IMPOSSIBLE);
    MATCH_MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
      OLTSTSU_WALL_AXIS_IMPOSSIBLE)] THEN
  UNDISCH_TAC `aN:real = aW` THEN DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[]);;

(* turnFrame and its inside (S12.turnFrame_inside) *)
let OLTSTP_TURN = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: nonpositive_impossible *)
let OLTSTP_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     oltstsu_ordinary cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     &0 < cW /\ sW <= &0 /\ --sW <= (&2 / &3) * cW /\ aN = aW /\
     ldisj cN sN uN vN aN cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = aW`)) THEN
  MATCH_MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`;
                `--sW:real`; `cW:real`; `vW:real`; `--uW - aW:real`; `aW:real`]
    OLTSTP_QUADRANT_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[oltstsu_quadrant; ldisj; OLTSTP_TURN] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC OLTSTSU_TOP_REFRAME THEN
    MAP_EVERY EXISTS_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
    ASM_REWRITE_TAC[OLTSTP_TURN];
    ASM_REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[]]);;

(* Lean: impossible_from_ordinary_input *)
let OLTSTP_IMPOSSIBLE_FROM_ORDINARY_INPUT = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     ocolti_input cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     &0 < cW /\ sW <= &0 /\ --sW <= (&2 / &3) * cW /\ aN = aW /\
     ldisj cN sN uN vN aN cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = aW`)) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`] OLTM_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `u1:real`
    (X_CHOOSE_THEN `v1:real` (X_CHOOSE_THEN `a1:real` STRIP_ASSUME_TAC))))) THEN
  MATCH_MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    OLTSTP_NONPOSITIVE_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[oltstsu_ordinary; ldisj] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[oltp_profile; ocolti_input; ldisj]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
