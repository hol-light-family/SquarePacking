(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMForwardPositiveDScalars.lean          *)
(* (N12Compact.C1092MPPMForwardPositiveD).  The two exact coefficient        *)
(* regimes in C1092-POSITIVE-D-TRANSFER.  CommonCases bounds is CCCS_BOUNDS. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let C1092FPD_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: coeffA *)
let c1092fpd_coeffA = new_definition
 `c1092fpd_coeffA (c:real) s f = c * (c + (&3 / &2) * s) - s * f + c + s - &2`;;

(* Lean: coeffB *)
let c1092fpd_coeffB = new_definition
 `c1092fpd_coeffB (c:real) s f = --s * (c + (&3 / &2) * s) - c * f + c - s + &87 / &50`;;

(* Lean: Coefficients *)
let c1092fpd_coefficients = new_definition
 `c1092fpd_coefficients c s f <=>
    &0 <= c1092fpd_coeffA c s f /\ c1092fpd_coeffB c s f <= &37 / &50 /\
    &0 < c1092fpd_coeffA c s f * s + c1092fpd_coeffB c s f * c /\
    f - ((&87 / &50) * c - &2 * s) < &1`;;

(* Lean: regime_one *)
let C1092FPD_REGIME_ONE = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\ &200 * s < &43 * c
     ==> c1092fpd_coefficients c s ((&113 / &50) * c - s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `s < &43 / &200` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&97 / &100 < c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092FPD_PROD `&0 <= (&97 / &100 - c) * (&97 / &100 + c)` THEN
   C1092FPD_PROD `&0 < (&43 / &200 - s) * (&43 / &200 + s)` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092fpd_coeffA c s ((&113 / &50) * c - s) =
                c + s - &1 - (&19 / &25) * c * s /\
                c1092fpd_coeffB c s ((&113 / &50) * c - s) =
                c - s - (&19 / &25) * c * c + &6 / &25` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092fpd_coeffA; c1092fpd_coeffB] THEN CONJ_TAC THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092fpd_coefficients] THEN
  C1092FPD_PROD `&0 <= c * s` THEN
  C1092FPD_PROD `&0 <= c * (&1 - c)` THEN
  C1092FPD_PROD `&0 <= (c - &1) * (c - &1)` THEN
  SUBGOAL_THEN `&0 <= c + s - &1 - (&19 / &25) * c * s /\
                &0 < c - s - (&19 / &25) * c * c + &6 / &25` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092FPD_PROD `&0 <= (c + s - &1 - (&19 / &25) * c * s) * s` THEN
  C1092FPD_PROD `&0 < (c - s - (&19 / &25) * c * c + &6 / &25) * c` THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: regime_two *)
let C1092FPD_REGIME_TWO = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
     ==> c1092fpd_coefficients c s (&2 * c - (&457 / &500) * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `c1092fpd_coeffA c s (&2 * c - (&457 / &500) * s) =
                c + s - &1 - (&1 / &2) * c * s - (&43 / &500) * s * s /\
                c1092fpd_coeffB c s (&2 * c - (&457 / &500) * s) =
                c - s - (&1 / &2) * c * c - (&43 / &500) * c * s + &6 / &25 /\
                c1092fpd_coeffA c s (&2 * c - (&457 / &500) * s) * s +
                c1092fpd_coeffB c s (&2 * c - (&457 / &500) * s) * c =
                &1 - (&13 / &50) * c - (&543 / &500) * s` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092fpd_coeffA; c1092fpd_coeffB] THEN REPEAT CONJ_TAC THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092fpd_coefficients] THEN
  C1092FPD_PROD `&0 <= c * s` THEN
  C1092FPD_PROD `&0 <= s * (c - s)` THEN
  C1092FPD_PROD `&0 <= (c - &1) * (c - &1)` THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;
