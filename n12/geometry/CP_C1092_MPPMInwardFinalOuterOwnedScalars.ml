(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalOuterOwnedScalars.lean    *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  INWARD-OUTER-OWNED-ANGLE:   *)
(* exact unit-circle identities and the half-angle interval.                 *)
(* Normal: c977cc_normal; half / quarter_data: C1092WPS_half /               *)
(* C1092WPS_QUARTER_DATA; normal_bounds: C977CC_NORMAL_BOUNDS;               *)
(* canonical_half_bounds: C1092IFAS_CANONICAL_HALF_BOUNDS; half_cross:       *)
(* C1092MIFE_HALF_CROSS; coordinates_after: C1092MIFSS_COORDINATES_AFTER.    *)
(* Real.sqrt 13 is sqrt(&13).  Tag C1092IFOO_.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalAngleScalars.ml";;

(* Lean: outer_short_width *)
let C1092IFOO_OUTER_SHORT_WIDTH = prove
 (`forall c s. c pow 2 + s pow 2 = &1
     ==> (&37 / &50) * c + (&3 / &5) * s < &1 /\ (&3 / &5) * c + (&37 / &50) * s < &1`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THENL
   [NLIN_TAC [SQ_NONNEG `(&3 / &5) * c - (&37 / &50) * s`;
              SQ_NONNEG `(&37 / &50) * c + (&3 / &5) * s - &1`];
    NLIN_TAC [SQ_NONNEG `(&37 / &50) * c - (&3 / &5) * s`;
              SQ_NONNEG `(&3 / &5) * c + (&37 / &50) * s - &1`]]);;

(* Lean: outer_lower_half *)
let C1092IFOO_OUTER_LOWER_HALF = prove
 (`forall c s. c977cc_normal c s /\ &1 < c + (&13 / &50) * s ==> C1092WPS_half c s < &13 / &50`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `z:real` THEN
  SUBGOAL_THEN `(&1 + z pow 2) * (c + (&13 / &50) * s - &1) = &2 * z * (&13 / &50 - z)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MIFS_PROD_TAC [`&0 < (&1 + z pow 2) * (c + (&13 / &50) * s - &1)`;
                      `&0 <= (&2 * z) * (z - &13 / &50)`] THEN
  RASM_ARITH_TAC);;

(* Lean: outer_upper_slope *)
let C1092IFOO_OUTER_UPPER_SLOPE = prove
 (`forall c s. c977cc_normal c s /\ &1 < (&37 / &50) * (c + s) ==> c < &2 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MIFS_PROD_TAC [`&0 <= (&2 * c - s) * (c - &2 * s)`;
                      `&0 < (c + s - &50 / &37) * (c + s + &50 / &37)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC);;

(* Lean: outer_q_identity *)
let C1092IFOO_OUTER_Q_IDENTITY = prove
 (`forall c s. c977cc_normal c s
     ==> (&1 + C1092WPS_half c s pow 2) * (&1 - c + (&13 / &50) * s - C1092WPS_half c s) =
         --(C1092WPS_half c s) * (C1092WPS_half c s pow 2 - &2 * C1092WPS_half c s + &12 / &25) /\
         c + s - &1 - c * s + (&13 / &50) * s pow 2 =
         s * (&1 - c + (&13 / &50) * s - C1092WPS_half c s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `z:real` THEN
  SUBGOAL_THEN `c - &1 + s * z = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + c) * (c - &1 + s * z) = &0` MP_TAC THENL
     [UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `c - &1 + s * z = &0` THEN CONV_TAC REAL_RING]);;

(* Lean: outer_angle_bounds *)
let C1092IFOO_OUTER_ANGLE_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\
         &0 < C1092WPS_half c s pow 2 - &2 * C1092WPS_half c s + &12 / &25
     ==> C1092WPS_half c s < &1 - sqrt(&13) / &5 /\ C1092WPS_half c s < &279 / &1000 /\
         &17 / &20 < c /\ s < &13 / &25`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFAS_CANONICAL_HALF_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&13) /\ sqrt(&13) pow 2 = &13` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_POS; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half c s < &279 / &1000` ASSUME_TAC THENL
   [ABBREV_TAC `z = C1092WPS_half c s` THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z - &279 / &1000) * (z + &279 / &1000 - &2) <= &0` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ABBREV_TAC `z = C1092WPS_half c s` THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (sqrt(&13) / &5 - (&1 - z)) * (sqrt(&13) / &5 + (&1 - z))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal (&922159 / &1077841) (&558000 / &1077841)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half (&922159 / &1077841) (&558000 / &1077841) = &279 / &1000`
    ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&922159 / &1077841`; `&558000 / &1077841`]
    C1092MIFE_HALF_CROSS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&922159 / &1077841`; `&558000 / &1077841`; `c:real`; `s:real`]
    C1092MIFSS_COORDINATES_AFTER) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: outer_halfpoint_projection *)
let C1092IFOO_OUTER_HALFPOINT_PROJECTION = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s < &1 / &3 ==> s + c / &2 < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `z:real` THEN
  SUBGOAL_THEN `(&1 + z pow 2) * (&1 - s - c / &2) = (&1 / &2) * (&1 - z) * (&1 - &3 * z)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MIFS_PROD_TAC [`&0 < (&1 - z) * (&1 - &3 * z)`;
                      `&0 <= (&1 + z pow 2) * (s + c / &2 - &1)`] THEN
  RASM_ARITH_TAC);;
