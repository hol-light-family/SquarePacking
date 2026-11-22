(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C702NorthScalars.lean              *)
(* (N12Compact.CommonCases.C702NorthScalars).  Scalar.                       *)
(* C981CompletionHalfAngle.half / data: c981ha_half / C981HA_DATA.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_HalfAngle.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;

let CCC702N_POW3 = REAL_ARITH `forall x:real. x pow 3 = x * x * x`;;

(* Lean: shallow_margin *)
let CCC702N_SHALLOW_MARGIN = prove
 (`forall c s. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\ &13 * s <= &9 * c
         ==> &1 < c + (&3 / &20) * c * s + (&7 / &20) * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981HA_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`c981ha_half c s`,`t:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(c + (&3 / &20) * c * s + (&7 / &20) * s pow 2 - &1) * (&10 * (&1 + t pow 2) pow 2) =
    t * (&3 - &6 * t - &3 * t pow 2 - &20 * t pow 3)` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + t pow 2) * c = &1 - t pow 2` THEN
    UNDISCH_TAC `(&1 + t pow 2) * s = &2 * t` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2; CCC702N_POW3]) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  NLIN_FACTS_TAC []
   [`&0 < t`;
    `&0 <= (&1 + t * t) * (&9 * c - &13 * s)`;
    `&9 * t * t + &26 * t <= &9`;
    `t < &8 / &25`;
    `&0 <= (&8 / &25 - t) * (&8 / &25 + t)`;
    `&0 <= (&8 / &25 - t) * ((&8 / &25) * (&8 / &25) + (&8 / &25) * t + t * t)`;
    `&0 < &3 - &6 * t - &3 * t * t - &20 * t * t * t`;
    `&0 < t * (&3 - &6 * t - &3 * t * t - &20 * t * t * t)`;
    `&0 < &10 * ((&1 + t * t) * (&1 + t * t))`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`(c + (&3 / &20) * c * s + (&7 / &20) * (s * s) - &1) *
     (&10 * ((&1 + t * t) * (&1 + t * t))) <= &0`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: steep_bounds *)
let CCC702N_STEEP_BOUNDS = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &9 * c < &13 * s
         ==> c < &5 / &6 /\ &14 / &25 < s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < (&13 * s - &9 * c) * (&13 * s + &9 * c)`] THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 <= (c - &5 / &6) * (c + &5 / &6)`];
    NLIN_FACTS_TAC [] [`&0 <= (&14 / &25 - s) * (&14 / &25 + s)`]] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_gap *)
let CCC702N_NEGATIVE_GAP = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &5 * c < &6 * s
         ==> (&63 / &50) * c < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < (&6 * s - &5 * c) * (&6 * s + &5 * c)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= (c - &50 / &63) * (c + &50 / &63)`] THEN
  NLIN_TAC ~deg2:false []);;
