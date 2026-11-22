(* ========================================================================= *)
(* Port of Compact/Completion/C981/HalfAngle.lean                             *)
(* (N12Compact.C981CompletionHalfAngle).  Half-angle identities on the       *)
(* canonical quarter circle.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: half (definition) *)
let c981ha_half = new_definition `c981ha_half (c:real) s = s / (&1 + c)`;;

(* Lean: data *)
let C981HA_DATA = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
     ==> &0 <= c981ha_half c s /\ c981ha_half c s <= &1 / &2 /\
         c981ha_half c s * (&1 + c) = s /\
         (&1 + (c981ha_half c s) pow 2) * c = &1 - (c981ha_half c s) pow 2 /\
         (&1 + (c981ha_half c s) pow 2) * s = &2 * c981ha_half c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c981ha_half c s * (&1 + c) = s` ASSUME_TAC THENL
  [REWRITE_TAC[c981ha_half] THEN UNDISCH_TAC `&0 <= c` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  UNDISCH_TAC `c981ha_half c s * (&1 + c) = s` THEN
  SPEC_TAC(`c981ha_half c s`,`t:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `s <= &1` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
   NLIN_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + c) * (&1 + t pow 2) = &2` ASSUME_TAC THENL
  [SUBGOAL_THEN `(&1 + c) * ((&1 + c) * (&1 + t pow 2) - &2) = &0` MP_TAC THENL
   [UNDISCH_TAC `t * (&1 + c) = s` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [NLIN_TAC []; NLIN_TAC [];
   UNDISCH_TAC `(&1 + c) * (&1 + t pow 2) = &2` THEN CONV_TAC REAL_RING;
   UNDISCH_TAC `(&1 + c) * (&1 + t pow 2) = &2` THEN
   UNDISCH_TAC `t * (&1 + c) = s` THEN CONV_TAC REAL_RING]);;

(* Lean: quarter_lt *)
let C981HA_QUARTER_LT = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &1 < s + (&3 / &5) * c
         ==> &1 / &4 < c981ha_half c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981HA_DATA) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`c981ha_half c s`,`t:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&1 + t pow 2) * (s + (&3 / &5) * c - &1) =
                (&2 / &5) * (&4 * t - &1) * (&1 - t)` ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + t pow 2) * c = &1 - t pow 2` THEN
   UNDISCH_TAC `(&1 + t pow 2) * s = &2 * t` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + t pow 2) * (s + (&3 / &5) * c - &1)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= --((&2 / &5) * (&4 * t - &1)) * (&1 - t)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: steep_lt *)
let C981HA_STEEP_LT = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &1 < s + (&11 / &25) * c
         ==> &7 / &18 < c981ha_half c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981HA_DATA) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`c981ha_half c s`,`t:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&1 + t pow 2) * (s + (&11 / &25) * c - &1) =
                (&2 / &25) * (&18 * t - &7) * (&1 - t)` ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + t pow 2) * c = &1 - t pow 2` THEN
   UNDISCH_TAC `(&1 + t pow 2) * s = &2 * t` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + t pow 2) * (s + (&11 / &25) * c - &1)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= --((&2 / &25) * (&18 * t - &7)) * (&1 - t)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: short_of_half *)
let C981HA_SHORT_OF_HALF = prove
 (`forall c s g. &0 <= c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ g < c981ha_half c s
           ==> c + g * s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `g * (&1 + c) < s` ASSUME_TAC THENL
  [UNDISCH_TAC `g < c981ha_half c s` THEN REWRITE_TAC[c981ha_half] THEN
   ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= c ==> &0 < &1 + c`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + c) * (c + g * s - &1) = s * (g * (&1 + c) - s)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + c) * (c + g * s - &1) /\ &0 < s * --(g * (&1 + c) - s)`
  MP_TAC THENL
  [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: sine38_short *)
let C981HA_SINE38_SHORT = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> s + (&19 / &50) * c < &1`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (c - s) * ((&1 + &2 * (&19 / &50) - (&19 / &50) * (&19 / &50)) * c +
                                 (&1 - &2 * (&19 / &50) - (&19 / &50) * (&19 / &50)) * s)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= ((&19 / &50) * c + s - &1) * ((&19 / &50) * c + s + &1)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
