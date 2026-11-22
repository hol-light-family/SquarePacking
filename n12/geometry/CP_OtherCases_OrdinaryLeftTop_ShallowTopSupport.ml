(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/ShallowTopSupport   *)
(* .lean (namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.       *)
(* ShallowTop).  Actual-square support argument of ORDINARY-LEFT-TOP       *)
(* Theorem 2 sections 2.2--2.3.                                             *)
(* lower / upper (ABTransverse): ABT_lower / ABT_upper; ownU: ABT_OWNU;     *)
(* S12.square_support_bound: SSB_SQUARE_SUPPORT_BOUND (p3);                 *)
(* C1092WholeSupports.lower_pn: C1092WS_LOWER_PN;                           *)
(* C981CompletionSupportForms.upper_in_bands: C981SF_UPPER_IN_BANDS;        *)
(* ShallowTopDirections.relative_coefficients: OLTSTD_RELATIVE_COEFFICIENTS;*)
(* ShallowTopExitScalars.wall_bounds: OLTSTE_WALL_BOUNDS;                   *)
(* ShallowTopScalars.*: OLTSTS_* / oltsts_*.                                *)
(* N = (cN, sN, uN, vN, aN), W = (cW, sW, uW, vW, aW); the OpenSquare        *)
(* invariants are explicit hypotheses.                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ShallowTopExitScalars.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ShallowTopDirections.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ShallowTopScalars.ml";;
needs "n12/geometry/CP_OtherCases_SupportBands.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/certlib/SquareSupportBase.ml";;

(* Lean: OrdinaryData (structure) *)
let oltstsu_ordinary = new_definition
 `oltstsu_ordinary (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\
    (&2 / &3) * c < s /\ s < (&8 / &11) * c /\
    --(&43 / &500) * c <= u /\
    --(&27 / &100) * s - (&1 / &25) * c <= v /\
    linside c s u v a (&13 / &20) (&7 / &20) /\
    linside c s u v a (&7 / &25) (&1)`;;

(* Lean: TopInput (structure) *)
let oltstsu_top = new_definition
 `oltstsu_top (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    linside c s u v a (&11 / &25) (&1) /\
    linside c s u v a (&1) (&1) /\
    linside c s u v a (&1) (&543 / &500) /\
    ~linside c s u v a (&63 / &50) (&1) /\
    (forall x y. linside c s u v a x y ==> y <= &2)`;;

(* Lean: TopInput.reframe *)
let OLTSTSU_TOP_REFRAME = prove
 (`forall c s u v a cr sr ur vr ar.
     oltstsu_top c s u v a /\
     (forall x y. linside cr sr ur vr ar x y <=> linside c s u v a x y)
     ==> oltstsu_top cr sr ur vr ar`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oltstsu_top] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: QuadrantData (structure) *)
let oltstsu_quadrant = new_definition
 `oltstsu_quadrant (c:real) (s:real) <=> &0 <= c /\ &0 < s /\ c <= (&2 / &3) * s`;;

(* Lean: alpha *)
let oltstsu_alpha = new_definition
 `oltstsu_alpha (cN:real) (sN:real) (cW:real) (sW:real) = cN * cW + sN * sW`;;

(* Lean: gamma *)
let oltstsu_gamma = new_definition
 `oltstsu_gamma (cN:real) (sN:real) (cW:real) (sW:real) = cN * sW - sN * cW`;;

(* Lean: coefficients *)
let OLTSTSU_COEFFICIENTS = prove
 (`forall cN sN uN vN aN cW sW.
     oltstsu_ordinary cN sN uN vN aN /\ oltstsu_quadrant cW sW
     ==> &0 < oltstsu_alpha cN sN cW sW /\ &0 < oltstsu_gamma cN sN cW sW`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oltstsu_ordinary; oltstsu_quadrant;
    oltstsu_alpha; oltstsu_gamma] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `cW:real`; `sW:real`]
    OLTSTD_RELATIVE_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: top_wall_faces *)
let OLTSTSU_TOP_WALL_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ oltstsu_top c s u v a /\ oltstsu_quadrant c s
     ==> s * (u + a) + c * (v + a) <= &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oltstsu_top; oltstsu_quadrant] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `&0`; `&1`; `&2`] SSB_SQUARE_SUPPORT_BOUND) THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_LID] THEN
  REWRITE_TAC[tss_support_radius; lcy; REAL_MUL_LZERO; REAL_MUL_LID;
              REAL_NEG_0; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`;
               REAL_ARITH `&0 < s ==> abs s = s`] THEN
  REAL_ARITH_TAC);;

(* Lean: lower_ordinary_normal *)
let OLTSTSU_LOWER_ORDINARY_NORMAL = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     oltstsu_ordinary cN sN uN vN aN /\ oltstsu_quadrant cW sW
     ==> ABT_lower cW sW uW vW aW cN sN =
         oltstsu_alpha cN sN cW sW * uW - oltstsu_gamma cN sN cW sW * (vW + aW)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`]
    OLTSTSU_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `cN:real`; `sN:real`;
                `oltstsu_alpha cN sN cW sW`; `--(oltstsu_gamma cN sN cW sW)`]
    C1092WS_LOWER_PN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[oltstsu_alpha; oltstsu_gamma] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[oltstsu_alpha; oltstsu_gamma]) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

(* Lean: upper_wall_normal *)
let OLTSTSU_UPPER_WALL_NORMAL = prove
 (`forall cN sN uN vN aN cW sW.
     oltstsu_ordinary cN sN uN vN aN /\ oltstsu_quadrant cW sW
     ==> ABT_upper cN sN uN vN aN cW sW =
         oltstsu_alpha cN sN cW sW * (uN + aN) + oltstsu_gamma cN sN cW sW * (vN + aN)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`]
    OLTSTSU_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[oltstsu_alpha; oltstsu_gamma] THEN STRIP_TAC THEN
  REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `cW * cN + sW * sN = cN * cW + sN * sW /\
                --cW * sN + sW * cN = cN * sW - sN * cW` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN REAL_ARITH_TAC);;

(* Lean: ordinary_axis_impossible *)
let OLTSTSU_ORDINARY_AXIS_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     oltstsu_ordinary cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     oltstsu_quadrant cW sW /\ aN = aW /\
     cW - (&63 / &50) * sW <= vW /\
     ABT_upper cN sN uN vN aN cN sN <= ABT_lower cW sW uW vW aW cN sN
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`]
    OLTSTSU_COEFFICIENTS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    OLTSTSU_TOP_WALL_FACES) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    OLTSTSU_LOWER_ORDINARY_NORMAL) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[oltstsu_alpha; oltstsu_gamma] THEN
  SUBGOAL_THEN `cW pow 2 + sW pow 2 = &1 /\ cN pow 2 + sN pow 2 = &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = aW`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[oltstsu_ordinary; oltstsu_quadrant]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    can (find_term ((=) `&13 / &20`)) (concl th))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    can (find_term ((=) `&2 / &3`)) (concl th) && is_conj(concl th))) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] OLTSTE_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`] OLTSTS_ORDINARY_PROJECTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(cN * (cW - &1 + sW * (&63 / &50 - cW)) + sN * sW * (&2 - sW)) - sW * ABT_lower cW sW uW vW aW cN sN =
    (cN * cW + sN * sW) * (&2 - sW * (uW + aW) - cW * (vW + aW)) +
    cN * (vW - (cW - (&63 / &50) * sW)) +
    (aW - &1) * ((cN * cW + sN * sW) * sW + cN)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhand(concl th) = `ABT_lower cW sW uW vW aW cN sN`
      then REWRITE_TAC[th] else NO_TAC) THEN
    UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (cN * cW + sN * sW) * (&2 - sW * (uW + aW) - cW * (vW + aW)) /\
                &0 <= cN * (vW - (cW - (&63 / &50) * sW)) /\
                &0 < (aW - &1) * ((cN * cW + sN * sW) * sW + cN) /\
                &0 <= cN * ((&1 - cW) * (&1 - sW)) /\
                &0 <= (sN * sW) * (sW - &4 / &5)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(FIRST
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC; MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
      MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC; MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(cN * (cW - &1 + sW * (&63 / &50 - cW)) + sN * sW * (&2 - sW)) <= sW * ((&13 / &50) * cN + (&6 / &5) * sN)` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= cN * ((&1 - cW) * (&1 - sW))` THEN
    UNDISCH_TAC `&0 <= (sN * sW) * (sW - &4 / &5)` THEN
    CONV_TAC REAL_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `sW * ((&13 / &50) * cN + (&6 / &5) * sN) < sW * (uN + aW) /\
                sW * (uN + aW) <= sW * ABT_lower cW sW uW vW aW cN sN` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST [MATCH_MP_TAC REAL_LT_LMUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: wall_axis_impossible *)
let OLTSTSU_WALL_AXIS_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     oltstsu_ordinary cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     oltstsu_quadrant cW sW /\ aN = aW /\
     cW - (&63 / &50) * sW <= vW /\
     ABT_upper cN sN uN vN aN cW sW <= ABT_lower cW sW uW vW aW cW sW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`]
    OLTSTSU_COEFFICIENTS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    OLTSTSU_TOP_WALL_FACES) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cW:real`; `sW:real`]
    OLTSTSU_UPPER_WALL_NORMAL) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[oltstsu_alpha; oltstsu_gamma] THEN
  SUBGOAL_THEN `cW pow 2 + sW pow 2 = &1 /\ cN pow 2 + sN pow 2 = &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = aW`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[oltstsu_ordinary; oltstsu_quadrant]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    can (find_term ((=) `&13 / &20`)) (concl th))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    can (find_term ((=) `&2 / &3`)) (concl th) && is_conj(concl th))) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `cW:real`; `sW:real`]
    OLTSTS_COEFFICIENT_RESIDUAL_POSITIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < oltsts_residual (oltsts_pcoeff cN sN) (oltsts_qcoeff cN sN) cW sW` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sW pow 2 / &30` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sW * (ABT_upper cN sN uN vN aW cW sW - uW) - oltsts_residual (oltsts_pcoeff cN sN) (oltsts_qcoeff cN sN) cW sW =
    sW * (cN * cW + sN * sW) * (uN + (&43 / &500) * cN) +
    sW * (cN * sW - sN * cW) * (vN + (&27 / &100) * sN + (&1 / &25) * cN) +
    (&2 - sW * (uW + aW) - cW * (vW + aW)) +
    cW * (vW - (cW - (&63 / &50) * sW)) +
    (aW - &1) * (sW * ((cN * cW + sN * sW) + (cN * sW - sN * cW)) + sW + cW)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhand(concl th) = `ABT_upper cN sN uN vN aW cW sW`
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[oltsts_residual; oltsts_pcoeff; oltsts_qcoeff] THEN
    UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sW * (cN * cW + sN * sW) * (uN + (&43 / &500) * cN) /\
                &0 <= sW * (cN * sW - sN * cW) * (vN + (&27 / &100) * sN + (&1 / &25) * cN) /\
                &0 <= cW * (vW - (cW - (&63 / &50) * sW)) /\
                &0 < (aW - &1) * (sW * ((cN * cW + sN * sW) + (cN * sW - sN * cW)) + sW + cW)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(FIRST
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC; MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
      MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC; MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `uW < ABT_upper cN sN uN vN aW cW sW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sW * (ABT_upper cN sN uN vN aW cW sW - uW) <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
