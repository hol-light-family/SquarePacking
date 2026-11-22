(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeProfileScalars.lean     *)
(* (N12Compact.C1092MPPMMissingNegativeProfile).  Normal: c977cc_normal;     *)
(* C1092WallProfileScalars.half / quarter_data: C1092WPS_half /              *)
(* C1092WPS_QUARTER_DATA.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

(* Lean: arc_gap *)
let C1092MNP_ARC_GAP = prove
 (`forall c s. c977cc_normal c s /\ &0 < s ==> (&413 / &500) * c * s < c + s - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c + s < &14143 / &10000` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PCT_PROD_TAC `c + s - &14143 / &10000` `c + s + &14143 / &10000` THEN
   NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  PCT_PRODLT_TAC `c:real` `s:real` THEN
  PCT_PRODLT_TAC `c * s` `&2 - (&413 / &500) * (&1 + c + s)` THEN
  SUBGOAL_THEN `(&1 + c + s) * (c + s - &1 - (&413 / &500) * c * s) =
                c * s * (&2 - (&413 / &500) * (&1 + c + s))` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 + c + s`; `c + s - &1 - (&413 / &500) * c * s`] PCT_POS_BY_POS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: half_width *)
let C1092MNP_HALF_WIDTH = prove
 (`forall c s b. c977cc_normal c s /\ &1 < b * c + s
           ==> &1 - b < (&1 + b) * C1092WPS_half c s /\ C1092WPS_half c s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c s`,`q:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&1 + q pow 2) * (b * c + s - &1) = (&1 - q) * ((&1 + b) * q - (&1 - b))`
  ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + q pow 2) * c = &1 - q pow 2` THEN
   UNDISCH_TAC `(&1 + q pow 2) * s = &2 * q` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  PCT_PRODLT_TAC `&1 + q pow 2` `b * c + s - &1` THEN
  SUBGOAL_THEN `&0 < (&1 - q) * ((&1 + b) * q - (&1 - b))` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q < &1` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `q = &1` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `&0 < (&1 - &1) * ((&1 + b) * &1 - (&1 - b))` THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`&1 - q`; `(&1 + b) * q - (&1 - b)`] PCT_POS_BY_POS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;
