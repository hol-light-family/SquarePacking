(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C702SouthScalars.lean              *)
(* (N12Compact.CommonCases.C702SouthScalars).  Two support margins for       *)
(* C702's southwest point.  Scalar.                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: shallow_margin *)
let CCC7SS_SHALLOW_MARGIN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &11 * s < c
         ==> &0 < &4 / &5 * c + &3 / &5 * s + &59 / &500 * s pow 2 -
                  &22 / &125 * c * s - &63 / &100`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
   [`c <= &1`; `&0 <= (c - &11 * s) * (c + &11 * s)`; `&11 / &12 < c`;
    `&0 <= s * (&3 / &5 - &22 / &125 * c)`] THEN
  NLIN_TAC []);;

(* Lean: negative_margin_dv (private) *)
let CCC7SS_NEGATIVE_MARGIN_DV = prove
 (`forall d v. &0 <= d /\ d <= &1 /\ &1 <= v /\ v pow 2 + d pow 2 = &2
         ==> &0 < (&4 / &5 - &419 / &1000 * d) * v + &3 / &5 * d +
                  &267 / &1000 * d pow 2 - &539 / &500`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= d * (&1 - d)`; `d * d <= &1`] THEN
  SUBGOAL_THEN `&0 <= (&1 - d * d) * (&1 + &4 * d * d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    MP_TAC(SPEC `d:real` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &5 - &2 / &5 * d * d <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 < (&7 / &5 - &2 / &5 * d * d - v) * (&7 / &5 - &2 / &5 * d * d + v)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&4 / &5 - &419 / &1000 * d) * (v - (&7 / &5 - &2 / &5 * d * d))`] THEN
  SUBGOAL_THEN `&0 <= d * ((d - &1 / &6) * (d - &1 / &6))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  MP_TAC(SPEC `d:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_margin *)
let CCC7SS_NEGATIVE_MARGIN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> &0 < &7 / &5 * c + &1 / &5 * s + &419 / &500 * s pow 2 -
                  &267 / &500 * c * s - &123 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c - s`; `c + s`] CCC7SS_NEGATIVE_MARGIN_DV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> &0 < x ==> &0 < y`) THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING);;
