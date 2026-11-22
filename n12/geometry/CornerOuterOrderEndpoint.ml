(* ========================================================================= *)
(* Port of Compact/Geometry/CornerOuterOrderEndpoint.lean (Jatloe).           *)
(* Exact endpoint of the bottom-to-wall angle comparison.                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* Lean: half_chord *)
let COOE_HALF_CHORD = prove
 (`forall d t. c977cc_normal d t ==> &1 - d <= t / &2`,
  REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&0 <= t * ((&1 + d) / &2 - t)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + d) * (t / &2 - (&1 - d)) = t * ((&1 + d) / &2 - t)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x - y ==> y <= x`) THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `&1 + d` THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* Lean: endpoint *)
let COOE_ENDPOINT = prove
 (`forall d t. c977cc_normal d t
     ==> (&2 * (d pow 2 - t pow 2) - (d + t) * (&1 - &2 * t + t * (&1 - t) / d)) *
         (d + t) + t - (d pow 2 - t pow 2) - &2 * d * t <= &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COOE_HALF_CHORD) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * ((d pow 2 + (&1 - d) pow 2) - &1 / &2)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(SPEC `d - &1 / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - d) * (t * (d pow 2 + (&1 - d) pow 2) - (&1 - d))`
  ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `d * ((&2 * (d pow 2 - t pow 2) - (d + t) * (&1 - &2 * t + t * (&1 - t) / d)) *
         (d + t) + t - (d pow 2 - t pow 2) - &2 * d * t) =
    (&1 - d) * ((&1 - d) - t * (d pow 2 + (&1 - d) pow 2))` ASSUME_TAC THENL
  [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPECL
   [`(&2 * (d pow 2 - t pow 2) - (d + t) * (&1 - &2 * t + t * (&1 - t) / d)) *
     (d + t) + t - (d pow 2 - t pow 2) - &2 * d * t`; `&0`; `d:real`]
   REAL_LE_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REAL_ARITH_TAC);;
