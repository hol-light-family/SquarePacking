(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/ShorterCornerScalars.lean           *)
(* (N12Compact.Completion.OtherCases.ShorterCornerScalars).  Exact quartic  *)
(* margin for the shorter actual corner reach.  Purely scalar.  Tag OSCS_.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: polynomial (private) *)
let OSCS_POLYNOMIAL = prove
 (`forall t. &0 <= t /\ t <= &1 / &2
       ==> &0 < &1 - &58 * t pow 2 + &200 * t pow 3 - &99 * t pow 4`,
  GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `t <= &3 / &10` THENL
   [SUBGOAL_THEN `&0 <= t pow 3 * (&200 - &99 * t - &1703 / &10) /\
                  &0 <= (t - &1160 / &5109) pow 2 * (t + (&1160 / &5109) / &2)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    SUBGOAL_THEN `&0 <= (t - &3 / &10) pow 3 * (&406 / &5 - &99 * (t - &3 / &10)) /\
                  &0 <= (t - &3 / &10) pow 2 /\ &0 <= t - &3 / &10`
    MP_TAC THENL
     [SUBGOAL_THEN `&0 <= t - &3 / &10` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* Lean: margin *)
let OSCS_MARGIN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> &0 < c + s - &1 - c * s + &1 / &50 * c pow 2 + &11 / &50 * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `C1092WPS_half c s <= &1 / &2` MP_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < c ==> &0 < &1 + c`] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c s`,`t:real`) THEN GEN_TAC THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:real` OSCS_POLYNOMIAL) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&50 * (&1 + t pow 2) pow 2 *
       (c + s - &1 - c * s + &1 / &50 * c pow 2 + &11 / &50 * s pow 2) =
       &1 - &58 * t pow 2 + &200 * t pow 3 - &99 * t pow 4` (SUBST1_TAC o SYM) THENL
   [UNDISCH_TAC `(&1 + t pow 2) * c = &1 - t pow 2` THEN
    UNDISCH_TAC `(&1 + t pow 2) * s = &2 * t` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &50 * (&1 + t pow 2) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_LT_MUL_EQ]);;
