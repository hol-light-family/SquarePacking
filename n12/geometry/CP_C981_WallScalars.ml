(* ========================================================================= *)
(* Port of Compact/Completion/C981/WallScalars.lean                           *)
(* (N12Compact.C981CompletionWallScalars).  Rational scalar inequalities for *)
(* the continuous C981 wall advance.                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C981WS_NONNEG_OF_MUL = prove
 (`forall x y. &0 < y /\ &0 <= y * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&0`; `x:real`; `y:real`] REAL_LE_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

(* Lean: wall_arc *)
let C981WS_WALL_ARC = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
         ==> (&93 / &100) * c * s <= c + s - &1 + (&6 / &25) * s pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s <= &1` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
   NLIN_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `exists t. t * (&1 + c) = s` STRIP_ASSUME_TAC THENL
  [EXISTS_TAC `s / (&1 + c)` THEN UNDISCH_TAC `&0 <= c` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t /\ t <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t`
  STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `(&1 + c) * (&1 + t pow 2) = &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + c) * ((&1 + c) * (&1 + t pow 2) - &2) = &0` MP_TAC THENL
    [UNDISCH_TAC `t * (&1 + c) = s` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
     CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THEN UNDISCH_TAC `(&1 + c) * (&1 + t pow 2) = &2` THEN
   UNDISCH_TAC `t * (&1 + c) = s` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &7 / &100 - (&13 / &25) * t + (&193 / &100) * t pow 2 - t pow 3`
  ASSUME_TAC THENL
  [ASM_CASES_TAC `t <= &1 / &2` THENL
   [SUBGOAL_THEN `&0 <= (&1 / &2 - t) * t pow 2` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    MP_TAC(SPEC `t - &2 / &11` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `t pow 3 = t * t * t`] THEN
    REPEAT DISCH_TAC THEN NLIN_TAC [];
    SUBGOAL_THEN `&0 <= (&1 - t) * t pow 2` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    MP_TAC(SPEC `t - &1 / &2` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `t pow 3 = t * t * t`] THEN
    REPEAT DISCH_TAC THEN NLIN_TAC []]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + t pow 2) pow 2 * (c + s - &1 + (&6 / &25) * s pow 2 - (&93 / &100) * c * s) =
    &2 * t * (&7 / &100 - (&13 / &25) * t + (&193 / &100) * t pow 2 - t pow 3)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + t pow 2) * c = &1 - t pow 2` THEN
   UNDISCH_TAC `(&1 + t pow 2) * s = &2 * t` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
  MATCH_MP_TAC C981WS_NONNEG_OF_MUL THEN EXISTS_TAC `(&1 + t pow 2) pow 2` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * t) *
     (&7 / &100 - (&13 / &25) * t + (&193 / &100) * t pow 2 - t pow 3)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC
   `(&1 + t pow 2) pow 2 * (c + s - &1 + (&6 / &25) * s pow 2 - (&93 / &100) * c * s) =
    &2 * t * (&7 / &100 - (&13 / &25) * t + (&193 / &100) * t pow 2 - t pow 3)` THEN
  REAL_ARITH_TAC);;

(* Lean: small_projection *)
let C981WS_SMALL_PROJECTION = prove
 (`forall c s. &50 / &53 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
         ==> (&89 / &100) * c + (&12 / &25) * s < &1`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s < &1 / &3` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < (c - &50 / &53) * (c + &50 / &53) /\
                 &0 <= (s - &1 / &3) * (s + &1 / &3)` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&53 * c - &150 * s) * (&983899 * c - &1295382 * s)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&89 * c + &48 * s - &100) * (&89 * c + &48 * s + &100)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: canonical_projection *)
let C981WS_CANONICAL_PROJECTION = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> (&143 / &500) * c + s < &1`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (c - s) * ((&1 + &2 * (&143 / &500) - (&143 / &500) * (&143 / &500)) * c +
                                 (&1 - &2 * (&143 / &500) - (&143 / &500) * (&143 / &500)) * s)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= ((&143 / &500) * c + s - &1) * ((&143 / &500) * c + s + &1)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
