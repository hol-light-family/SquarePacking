(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/OutwardScalars.lean                *)
(* (N12Compact.CommonCases.OutwardScalars).  Scalar.                         *)
(* The three half-angle projections share one comparison lemma with an       *)
(* exact rational boundary point (c0,s0) on the unit circle.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: increasing_projection *)
let CCOS_INCREASING_PROJECTION = prove
 (`forall c s a b. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
             &0 <= a /\ a <= b /\ (a + b) * (&99 / &140) < &1
             ==> a * c + b * s < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s:real`]
   [`c + s < &99 / &70`; `&0 <= (b - a) * (c - s)`;
    `&0 <= (a + b) * (&99 / &70 - (c + s))`] THEN
  NLIN_TAC ~deg2:false []);;

(* the common core of shallow_projection, short_strong_projection and       *)
(* strong_bar_projection (Lean repeats it inline three times)               *)
let CCOS_HALF_ANGLE_COMPARE = prove
 (`forall c s k c0 s0.
      &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\ &0 < k /\
      &1 < c + k * s /\
      c0 pow 2 + s0 pow 2 = &1 /\ &0 < c0 /\ &0 < s0 /\ s0 <= c0 /\
      s0 = k * (&1 + c0)
      ==> s <= s0 /\ c0 <= c /\ c + s <= c0 + s0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s < k * (&1 + c)` ASSUME_TAC THENL
   [NLIN_FACTS_TAC []
     [`(&1 - c) * (&1 + c) < (k * s) * (&1 + c)`;
      `s * s < k * s * (&1 + c)`] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`s * (k * (&1 + c)) <= s * s`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `s <= s0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (s - s0) * (s + s0)`; `c < c0`] THEN
    NLIN_FACTS_TAC [] [`k * (&1 + c) < k * (&1 + c0)`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  NLIN_FACTS_TAC [] [`&0 <= (s0 - s) * (s0 + s)`; `c0 <= c`] THEN
  ASM_REWRITE_TAC[] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - c0) * ((c + c0) - (s + s0))`;
    `&0 <= (c0 + s0 - c - s) * (s + s0)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`(c0 + s0 - c - s) * (s + s0) < &0`] THEN
  ASM_REAL_ARITH_TAC);;

let CCOS_PROJ_TAC k c0 s0 =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; k; c0; s0] CCOS_HALF_ANGLE_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REAL_ARITH_TAC;;

(* Lean: shallow_projection *)
let CCOS_SHALLOW_PROJECTION = prove
 (`forall c s. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &1 < c + &143 / &500 * s
         ==> &27 / &50 * c + &101 / &100 * s < &1`,
  CCOS_PROJ_TAC `&143 / &500` `&229551 / &270449` `&143000 / &270449`);;

(* Lean: short_strong_projection *)
let CCOS_SHORT_STRONG_PROJECTION = prove
 (`forall c s. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &1 < c + &89 / &250 * s
         ==> &23 / &50 * c + &101 / &100 * s < &1`,
  CCOS_PROJ_TAC `&89 / &250` `&54579 / &70421` `&44500 / &70421`);;

(* Lean: strong_bar_projection *)
let CCOS_STRONG_BAR_PROJECTION = prove
 (`forall c s. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &1 < c + &113 / &500 * s
         ==> &313 / &500 * c + &101 / &100 * s < &1`,
  CCOS_PROJ_TAC `&113 / &500` `&237231 / &262769` `&113000 / &262769`);;
