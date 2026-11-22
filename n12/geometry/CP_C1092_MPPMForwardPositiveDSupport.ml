(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMForwardPositiveDSupport.lean          *)
(* (N12Compact.C1092MPPMForwardPositiveD).  The recipient-normal            *)
(* comparisons in C1092-POSITIVE-D-TRANSFER sections 4--5.  Square C is     *)
(* c s u v a; of the recipient square J only its normal (cJ, sJ) enters.     *)
(* upper is ABT_upper, WallProfile.upper_in_bands is OCWPSG_UPPER_IN_BANDS;  *)
(* Coefficients / coeffA / coeffB are c1092fpd_*.  Tag C1092FPDS_.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMForwardPositiveDFaces.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let C1092FPDS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: coefficient_tilt (private) *)
let C1092FPDS_COEFFICIENT_TILT = prove
 (`forall c s d t f. &0 < c /\ &0 < d /\ c1092fpd_coefficients c s f /\ &0 <= c * t - s * d
     ==> &0 < c1092fpd_coeffA c s f * t + c1092fpd_coeffB c s f * d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092fpd_coefficients] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c * (c1092fpd_coeffA c s f * t + c1092fpd_coeffB c s f * d)` MP_TAC THENL
   [C1092FPDS_PROD_TAC
     [`&0 <= c1092fpd_coeffA c s f * (c * t - s * d)`;
      `&0 < d * (c1092fpd_coeffA c s f * s + c1092fpd_coeffB c s f * c)`] THEN
    RASM_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_MUL_EQ]]);;

(* Lean: recipient_u *)
let C1092FPDS_RECIPIENT_U = prove
 (`forall c s u v a cJ sJ f.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\ &0 < cJ /\ &0 <= sJ /\
     c + (&3 / &2) * s <= u /\ v + a <= f /\
     linside c s u v a (&87 / &50) (&2) /\ c1092fpd_coefficients c s f
     ==> &2 * cJ + sJ < ABT_upper c s u v a cJ sJ`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `c1092fpd_coefficients c s f`) THEN
  REWRITE_TAC[c1092fpd_coefficients] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `linside c s u v a (&87 / &50) (&2)`) THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  C1092FPDS_PROD_TAC [`&0 < c * cJ`; `&0 <= s * sJ`] THEN
  SUBGOAL_THEN `&0 < c * cJ + s * sJ` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(cJ * c + sJ * s) = c * cJ + s * sJ` SUBST1_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c * sJ - s * cJ` THENL
   [SUBGOAL_THEN `abs(--cJ * s + sJ * c) = c * sJ - s * cJ` SUBST1_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(c * cJ + s * sJ) * (&2 * c + s) + (c * sJ - s * cJ) * (c - &2 * s) =
                  &2 * cJ + sJ` ASSUME_TAC THENL
     [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092FPDS_PROD_TAC
     [`&0 <= (c * cJ + s * sJ) * (u - (c + (&3 / &2) * s))`;
      `&0 <= (c * sJ - s * cJ) * ((v + a) - (--s * &87 / &50 + c * &2))`;
      `&0 < (c * cJ + s * sJ) * (a - c + s / &2)`;
      `&0 <= (c * sJ - s * cJ) * (c + (&13 / &50) * s)`] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `abs(--cJ * s + sJ * c) = --(c * sJ - s * cJ)` SUBST1_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    C1092FPDS_PROD_TAC
     [`&0 <= (c * cJ + s * sJ) * (u - (c + (&3 / &2) * s))`;
      `&0 <= --(c * sJ - s * cJ) * (f - (v + a))`;
      `&0 < (a - &1) * ((c * cJ + s * sJ) + --(c * sJ - s * cJ))`;
      `&0 <= c1092fpd_coeffA c s f * cJ`;
      `&0 <= (&37 / &50 - c1092fpd_coeffB c s f) * sJ`] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[c1092fpd_coeffA; c1092fpd_coeffB] THEN
    REPEAT DISCH_TAC THEN RASM_ARITH_TAC]);;

(* Lean: recipient_negative_v *)
let C1092FPDS_RECIPIENT_NEGATIVE_V = prove
 (`forall c s u v a cJ sJ f.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ &0 < cJ /\ &0 <= sJ /\
     c + (&3 / &2) * s <= u /\ v + a <= f /\
     linside c s u v a (&1) (&8 / &5) /\ c1092fpd_coefficients c s f
     ==> &2 * sJ - (&87 / &50) * cJ < ABT_upper c s u v a sJ (--cJ)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `c1092fpd_coefficients c s f`) THEN
  REWRITE_TAC[c1092fpd_coefficients] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `linside c s u v a (&1) (&8 / &5)`) THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  C1092FPDS_PROD_TAC [`&0 < c * cJ`; `&0 <= s * sJ`] THEN
  SUBGOAL_THEN `&0 < c * cJ + s * sJ` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(--sJ * s + --cJ * c) = c * cJ + s * sJ` SUBST1_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c * sJ - s * cJ` THENL
   [SUBGOAL_THEN `abs(sJ * c + --cJ * s) = c * sJ - s * cJ` SUBST1_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `cJ:real`; `sJ:real`; `f:real`]
      C1092FPDS_COEFFICIENT_TILT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    C1092FPDS_PROD_TAC
     [`&0 <= (c * sJ - s * cJ) * (u - (c + (&3 / &2) * s))`;
      `&0 <= (c * cJ + s * sJ) * (f - (v + a))`;
      `&0 < (a - &1) * ((c * cJ + s * sJ) + (c * sJ - s * cJ))`] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[c1092fpd_coeffA; c1092fpd_coeffB] THEN
    REPEAT DISCH_TAC THEN RASM_ARITH_TAC;
    SUBGOAL_THEN `abs(sJ * c + --cJ * s) = --(c * sJ - s * cJ)` SUBST1_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `--(--(c * sJ - s * cJ)) * (&2 * c + (&87 / &50) * s) -
                  (c * cJ + s * sJ) * ((&87 / &50) * c - &2 * s) =
                  &2 * sJ - (&87 / &50) * cJ` ASSUME_TAC THENL
     [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092FPDS_PROD_TAC
     [`&0 <= --(c * sJ - s * cJ) * ((c * &1 + s * &8 / &5) - u)`;
      `&0 <= (c * cJ + s * sJ) * (f - (v + a))`;
      `&0 < (c * cJ + s * sJ) * (a + ((&87 / &50) * c - &2 * s) - f)`;
      `&0 <= --(c * sJ - s * cJ) * (c + (&7 / &50) * s)`] THEN
    RASM_ARITH_TAC]);;
