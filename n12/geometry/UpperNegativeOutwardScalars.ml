(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeOutwardScalars.lean (Jatloe,      *)
(* N12-jatloe; N12Compact.C868.UpperNegativeOutwardScalars).  Small exact     *)
(* support margins for the negative merged-upper / outward southeast pair.   *)
(* Scalar; tag C868OS_.  Normal: c977cc_normal; UnitCircleChord.increasing / *)
(* decreasing: CCUCC_INCREASING / CCUCC_DECREASING.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

(* Instantiate a scalar lemma, discharging its side conditions by numerals, *)
(* assumptions or linear arithmetic.                                         *)
let C868OS_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN
   FIRST [CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
          FIRST_ASSUM ACCEPT_TAC; NLIN_TAC ~deg2:false []];
   CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN DISCH_TAC];;

let C868OS_NORMAL_ASSUME th =
  STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th);;

(* Lean: steep_of_projection *)
let C868OS_STEEP_OF_PROJECTION = prove
 (`forall c s. c977cc_normal c s /\ &1000 < &525 * c + &961 * s
         ==> &3 / &5 < s /\ c < &4 / &5`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun h ->
    C868OS_NORMAL_ASSUME (CONJUNCT1 h) THEN ASSUME_TAC(CONJUNCT2 h)) THEN
  SUBGOAL_THEN `&3 / &5 < s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C868OS_USE CCUCC_INCREASING [`&4 / &5`; `&3 / &5`; `c:real`; `s:real`;
                                `&525`; `&961`] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - &4 / &5) * (c + &4 / &5)`; `&0 < (s - &3 / &5) * (s + &3 / &5)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: outward_sine_cap *)
let C868OS_OUTWARD_SINE_CAP = prove
 (`forall d t. c977cc_normal d t /\ &1 < d + (&143 / &500) * t
         ==> t < &143000 / &270449`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun h ->
    C868OS_NORMAL_ASSUME (CONJUNCT1 h) THEN ASSUME_TAC(CONJUNCT2 h)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C868OS_USE CCUCC_DECREASING [`&229551 / &270449`; `&143000 / &270449`;
                               `d:real`; `t:real`; `&1`; `&143 / &500`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: coefficients (private) *)
let C868OS_COEFFICIENTS = prove
 (`forall c s. c977cc_normal c s /\ &3 / &5 <= s /\ c <= &4 / &5
         ==> &1 - c - s + (&543 / &500) * c * s + (&13 / &50) * s pow 2 <= &13 / &50 /\
             &1 + c - s - (&13 / &50) * c * s + (&543 / &500) * s pow 2 <= &147 / &100`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun h ->
    C868OS_NORMAL_ASSUME (CONJUNCT1 h) THEN STRIP_ASSUME_TAC(CONJUNCT2 h)) THEN
  NLIN_FACTS_TAC []
   [`&0 <= c - s`; `c - s <= &1 / &5`; `&0 <= c + s`] THEN
  SUBGOAL_THEN `(c + s) pow 2 + (c - s) pow 2 = &2` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&1 / &5 - (c - s)) * (&1 / &5 + (c - s))`] THEN
  NLIN_FACTS_TAC [] [`(c - s) pow 2 <= &1 / &25`] THEN
  SUBGOAL_THEN `&7 / &5 <= c + s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   NLIN_FACTS_TAC [] [`&0 < (&7 / &5 - (c + s)) * (&7 / &5 + (c + s))`] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `c + s <= &99 / &70` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   NLIN_FACTS_TAC [] [`&0 < ((c + s) - &99 / &70) * ((c + s) + &99 / &70)`] THEN
   NLIN_TAC ~deg2:false [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c + s) * (c - s)`;
    `&0 <= (&99 / &70 - (c + s)) * ((&543 / &1000) * (&99 / &70 + (c + s)) - &1)`;
    `&0 <= (c - s) * ((c + s) - &7 / &5)`] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: right_axis_margin *)
let C868OS_RIGHT_AXIS_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &1000 < &525 * c + &961 * s /\ &1 < d + (&143 / &500) * t
             ==> &1 / &500 <= &1 + (c * d + s * t) + (s * d - c * t) - d - t -
                   s * ((&543 / &500) * (c * d + s * t) + (&13 / &50) * (s * d - c * t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C868OS_STEEP_OF_PROJECTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C868OS_COEFFICIENTS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C868OS_OUTWARD_SINE_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C868OS_NORMAL_ASSUME (ASSUME `c977cc_normal d t`) THEN
  C868OS_USE CCUCC_INCREASING [`&229551 / &270449`; `&143000 / &270449`;
                               `d:real`; `t:real`; `&13 / &50`; `&147 / &100`] THEN
  NLIN_FACTS_TAC []
   [`&0 <= d * (&13 / &50 - (&1 - c - s + (&543 / &500) * c * s + (&13 / &50) * s pow 2))`;
    `&0 <= t * (&147 / &100 - (&1 + c - s - (&13 / &50) * c * s + (&543 / &500) * s pow 2))`] THEN
  NLIN_TAC ~deg2:false []);;
