(* ========================================================================= *)
(* Port of Compact/Geometry/ScalarSATPositive.lean (N12Compact.SATPositive). *)
(* Scalar SAT, positive relative orientation (half-side 1 coordinates).     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ScalarSATIntervals.ml";;

(* Lean: positive_overlap *)
let SSP_POSITIVE_OVERLAP = prove
 (`forall c s X Y U V.
     &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < &1 + c + s /\ abs Y < &1 + c + s /\
     abs U < &1 + c + s /\ abs V < &1 + c + s
     ==> exists x y. abs x < &1 /\ abs y < &1 /\
               abs(c * x + s * y - U) < &1 /\ abs(--s * x + c * y - V) < &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SSI_POSITIVE_Y_INTERVALS) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s * U + c * V = Y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c * c + s * s = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `exists x. (--(&1) < x /\ (U - &1 - s * y) / c < x /\ (c * y - V - &1) / s < x) /\
        (x < &1 /\ x < (U + &1 - s * y) / c /\ x < (c * y - V + &1) / s)`
  MP_TAC THENL
   [MATCH_MP_TAC SSI_BETWEEN_THREE THEN
    SIMP_TAC[SSI_DIV_LT_DIV; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
    REPEAT CONJ_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN
  REWRITE_TAC[SSI_ABS_LT] THEN RASM_ARITH_TAC);;

(* Lean: nonnegative_overlap *)
let SSP_NONNEGATIVE_OVERLAP = prove
 (`forall c s X Y U V.
     &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < &1 + c + s /\ abs Y < &1 + c + s /\
     abs U < &1 + c + s /\ abs V < &1 + c + s
     ==> exists x y. abs x < &1 /\ abs y < &1 /\
               abs(c * x + s * y - U) < &1 /\ abs(--s * x + c * y - V) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `c = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `s = &1` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
      UNDISCH_TAC `&0 pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
      DISCH_TAC THEN CONJ_TAC THEN NLIN_TAC [];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`X / &2`; `Y / &2`] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `c = &1` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
      UNDISCH_TAC `c pow 2 + &0 pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
      DISCH_TAC THEN CONJ_TAC THEN NLIN_TAC [];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`X / &2`; `Y / &2`] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SSP_POSITIVE_OVERLAP THEN EXISTS_TAC `X:real` THEN EXISTS_TAC `Y:real` THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;
