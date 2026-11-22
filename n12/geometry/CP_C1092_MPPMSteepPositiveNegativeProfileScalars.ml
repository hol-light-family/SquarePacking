(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMSteepPositiveNegativeProfileScalars  *)
(* .lean (N12Compact.C1092MPPMSteepPositiveNegativeProfile.Scalars).         *)
(* Finite circle identities for STEEP-POSITIVE-NEGATIVE-PROFILE.            *)
(* Normal is c977cc_normal; norm_le is C1092NPP_NORM_LE; canonical_bounds is *)
(* C1092PRS_CANONICAL_BOUNDS.                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessorScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;

(* Lean: Pu, Qu, Pv, Qv, f, B (definitions) *)
let c1092snp_Pu = new_definition
 `c1092snp_Pu (d:real) (t:real) = &2 - d - (&37 / &50) * t pow 2`;;
let c1092snp_Qu = new_definition
 `c1092snp_Qu (d:real) (t:real) = t * (&1 - (&37 / &50) * d)`;;
let c1092snp_Pv = new_definition
 `c1092snp_Pv (d:real) = &13 / &50 + (&37 / &50) * d pow 2 - d`;;
let c1092snp_Qv = new_definition
 `c1092snp_Qv (d:real) (t:real) = &1 + t - (&37 / &50) * d * t`;;
let c1092snp_f = new_definition
 `c1092snp_f (c:real) (s:real) = &1 + c * s - c - s`;;
let c1092snp_B = new_definition
 `c1092snp_B (c:real) (s:real) = c - s + s pow 2 - &13 / &50`;;

(* Lean: current_margin *)
let C1092SNP_CURRENT_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 <= &1 - c1092snp_Pu d t * c - c1092snp_Qu d t * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c1092snp_Pu d t`; `c1092snp_Qu d t`; `c:real`; `s:real`; `&1`]
    C1092NPP_NORM_LE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_LT_01] THEN
   C1092PRS_PROD `&0 <= (&1 - d) * (&6031 * d - &3969)` THEN
   SUBGOAL_THEN `&1 - c1092snp_Pu d t pow 2 - c1092snp_Qu d t pow 2 =
                 (&1 - d) * (&6031 * d - &3969) / &2500` MP_TAC THENL
   [REWRITE_TAC[c1092snp_Pu; c1092snp_Qu] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   UNDISCH_TAC `&0 <= (&1 - d) * (&6031 * d - &3969)` THEN REAL_ARITH_TAC;
   REAL_ARITH_TAC]);;

(* Lean: transverse_margin *)
let C1092SNP_TRANSVERSE_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 < &1 - c1092snp_Pv d * c - c1092snp_Qv d t * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  REWRITE_TAC[c1092snp_Pv; c1092snp_Qv] THEN
  C1092PRS_PROD `&0 <= (&1 - d) * ((&37 / &50) * d - &13 / &50)` THEN
  C1092PRS_PROD `&0 <= t * (d - &7 / &10)` THEN
  SUBGOAL_THEN `&13 / &50 + (&37 / &50) * d pow 2 - d <= &0 /\
                &1 + t - (&37 / &50) * d * t < &7 / &5` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= --(&13 / &50 + (&37 / &50) * d pow 2 - d) * c` THEN
  C1092PRS_PROD `&0 <= (&7 / &5 - (&1 + t - (&37 / &50) * d * t)) * s` THEN
  RASM_ARITH_TAC);;

(* Lean: envelope *)
let C1092SNP_ENVELOPE = prove
 (`forall c s. c977cc_normal c s ==> c1092snp_f c s < &43 / &500 /\ &6 / &25 <= c1092snp_B c s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `c + s < &99 / &70` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`; SQ_NONNEG `c + s - &99 / &70`]; ALL_TAC] THEN
  C1092PRS_PROD `&0 < (&99 / &70 - c - s) * (&99 / &70 + c + s - &2)` THEN
  C1092PRS_PROD `&0 <= (c - s) * (&1 - (c + s) / &2)` THEN
  REWRITE_TAC[c1092snp_f; c1092snp_B] THEN CONJ_TAC THEN RASM_ARITH_TAC);;
