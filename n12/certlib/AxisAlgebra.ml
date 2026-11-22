(* ========================================================================= *)
(* Port of source/S12/AxisAlgebra.lean (Jatloe, N12-jatloe).                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/SquareSupportBase.ml";;

(* Lean: planeL1 *)
let planeL1 = new_definition
 `planeL1 c s x y = abs(c * x + s * y) + abs(--s * x + c * y)`;;

(* Lean: AxisOverlap *)
let axis_overlap = new_definition
 `axis_overlap a b c s dx dy <=>
    abs dx < a + b * (c + s) /\ abs dy < a + b * (c + s) /\
    abs(c * dx + s * dy) < b + a * (c + s) /\ abs(--s * dx + c * dy) < b + a * (c + s)`;;

(* Lean: weighted_two_lt *)
let AXA_WEIGHTED_TWO_LT = prove
 (`forall x y u v A B. &0 <= A /\ &0 <= B /\ (~(A = &0) \/ ~(B = &0)) /\ x < u /\ y < v
     ==> A * x + B * y < A * u + B * v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
  NLIN_TAC []);;

let AXA_LT_LCANCEL = prove
 (`forall z x y. &0 < z /\ z * x < z * y ==> x < y`,
  MESON_TAC[REAL_LT_LMUL_EQ]);;

(* Lean: positive_normal_gap *)
let AXA_POSITIVE_NORMAL_GAP = prove
 (`forall a b c s dx dy nx ny.
     &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
     axis_overlap a b c s dx dy /\ &0 <= nx /\ &0 <= ny /\ (~(nx = &0) \/ ~(ny = &0))
     ==> nx * dx + ny * dy < a * (nx + ny) + b * planeL1 c s nx ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[axis_overlap; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `dx < a + b * (c + s) /\ dy < a + b * (c + s) /\
                c * dx + s * dy < b + a * (c + s)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c = &0` THENL
   [SUBGOAL_THEN `s = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ &1 <= x ==> x = &1`) THEN
      CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`dx:real`; `dy:real`; `a + b`; `a + b`; `nx:real`; `ny:real`]
      AXA_WEIGHTED_TWO_LT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[planeL1] THEN ASM_SIMP_TAC[REAL_ARITH
      `&0 <= nx /\ &0 <= ny ==> abs(&0 * nx + &1 * ny) + abs(--(&1) * nx + &0 * ny) = nx + ny`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL
   [SUBGOAL_THEN `c = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ &1 <= x ==> x = &1`) THEN
      CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`dx:real`; `dy:real`; `a + b`; `a + b`; `nx:real`; `ny:real`]
      AXA_WEIGHTED_TWO_LT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[planeL1] THEN ASM_SIMP_TAC[REAL_ARITH
      `&0 <= nx /\ &0 <= ny ==> abs(&1 * nx + &0 * ny) + abs(--(&0) * nx + &1 * ny) = nx + ny`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c /\ &0 < s` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * nx + s * ny` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  ASM_CASES_TAC `c * ny <= s * nx` THENL
   [SUBGOAL_THEN `planeL1 c s nx ny = c * nx + s * ny + s * nx - c * ny` SUBST1_TAC THENL
     [REWRITE_TAC[planeL1] THEN MP_TAC(ASSUME `&0 <= c * nx + s * ny`) THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC AXA_LT_LCANCEL THEN EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`dx:real`; `c * dx + s * dy`; `a + b * (c + s)`; `b + a * (c + s)`;
                  `s * nx - c * ny`; `ny:real`] AXA_WEIGHTED_TWO_LT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `ny = &0` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(nx = &0) \/ ~(ny = &0)` THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ENTIRE];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = x' /\ y = y' ==> x < y ==> x' < y'`) THEN
    CONJ_TAC THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
    SUBGOAL_THEN `planeL1 c s nx ny = c * nx + s * ny - s * nx + c * ny` SUBST1_TAC THENL
     [REWRITE_TAC[planeL1] THEN MP_TAC(ASSUME `&0 <= c * nx + s * ny`) THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC AXA_LT_LCANCEL THEN EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c * dx + s * dy`; `dy:real`; `b + a * (c + s)`; `a + b * (c + s)`;
                  `nx:real`; `c * ny - s * nx`] AXA_WEIGHTED_TWO_LT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `nx = &0` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(nx = &0) \/ ~(ny = &0)` THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ENTIRE];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = x' /\ y = y' ==> x < y ==> x' < y'`) THEN
    CONJ_TAC THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING]);;
