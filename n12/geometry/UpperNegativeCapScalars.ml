(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeCapScalars.lean (Jatloe,          *)
(* N12-jatloe; N12Compact.C868.UpperNegativeCapScalars).  Exact full-arc     *)
(* vertex bounds in the remaining upper-V branch.  Scalar; tag C868CSC_.     *)
(* Normal: c977cc_normal; CanonicalProjection.before/after: CCCP_BEFORE /    *)
(* CCCP_AFTER; UnitCircleChord.increasing/cosine_order: CCUCC_INCREASING /   *)
(* CCUCC_COSINE_ORDER.  Private c0 = 609/641, s0 = 200/641 are inlined.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

(* Instantiate a scalar lemma, discharging its side conditions by numerals, *)
(* assumptions or linear arithmetic.                                         *)
let C868CSC_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN
   FIRST [CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
          FIRST_ASSUM ACCEPT_TAC; NLIN_TAC ~deg2:false []];
   CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN DISCH_TAC];;

let C868CSC_SETUP ths =
  REPEAT GEN_TAC THEN DISCH_THEN(fun h ->
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC(MATCH_MP th h)) ths THEN
    STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (CONJUNCT1 h)) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] h));;

(* Lean: angle *)
let C868CSC_ANGLE = prove
 (`forall c s. c977cc_normal c s /\
         &1 < (&18 / &25) * c + (&99 / &100) * s /\
         &1 < (&142 / &125) * c + (&1 / &20) * s
         ==> &5 * s < &3 * c`,
  C868CSC_SETUP [] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C868CSC_USE CCCP_AFTER [`c:real`; `s:real`; `&3901 / &4549`; `&2340 / &4549`;
                          `&142 / &125`; `&1 / &20`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: region (private) *)
let C868CSC_REGION = prove
 (`forall c s. c977cc_normal c s /\
         &1 < (&18 / &25) * c + (&99 / &100) * s /\
         &1 < (&142 / &125) * c + (&1 / &20) * s
         ==> &17 / &20 <= c /\ c <= &609 / &641 /\ &200 / &641 <= s /\
             s <= &13 / &25`,
  C868CSC_SETUP [C868CSC_ANGLE] THEN
  SUBGOAL_THEN `&200 / &641 <= s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C868CSC_USE CCUCC_INCREASING [`&609 / &641`; `&200 / &641`; `c:real`; `s:real`;
                                 `&18 / &25`; `&99 / &100`] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C868CSC_USE CCUCC_COSINE_ORDER [`&609 / &641`; `&200 / &641`; `c:real`; `s:real`] THEN
  NLIN_FACTS_TAC [] [`&0 < (&3 * c - &5 * s) * (&3 * c + &5 * s)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   NLIN_FACTS_TAC [] [`(c - &17 / &20) * (c + &17 / &20) < &0`] THEN
   NLIN_TAC ~deg2:false [];
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   NLIN_FACTS_TAC [] [`&0 < (s - &13 / &25) * (s + &13 / &25)`] THEN
   NLIN_TAC ~deg2:false []]);;

(* Lean: chord_slope (private) *)
let C868CSC_CHORD_SLOPE = prove
 (`forall c s. c977cc_normal c s /\
         &1 < (&18 / &25) * c + (&99 / &100) * s /\
         &1 < (&142 / &125) * c + (&1 / &20) * s
         ==> &609 / &641 - c <= (&47 / &100) * (s - &200 / &641)`,
  C868CSC_SETUP [C868CSC_ANGLE; C868CSC_REGION] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&47 / &100) * (c + &609 / &641) - (s + &200 / &641)`;
    `&0 <= (s - &200 / &641) *
           ((&47 / &100) * (c + &609 / &641) - (s + &200 / &641))`;
    `&0 <= ((&47 / &100) * (s - &200 / &641) - (&609 / &641 - c)) *
           (c + &609 / &641)`;
    `&0 < c + &609 / &641`] THEN
  NLIN_TAC []);;

(* Lean: height *)
let C868CSC_HEIGHT = prove
 (`forall c s. c977cc_normal c s /\
         &1 < (&18 / &25) * c + (&99 / &100) * s /\
         &1 < (&142 / &125) * c + (&1 / &20) * s
         ==> &53 / &50 < c + s - (&51 / &100) * c * s + (&1 / &100) * s pow 2 -
                         (&1 / &20) * c pow 2`,
  C868CSC_SETUP [C868CSC_ANGLE; C868CSC_REGION; C868CSC_CHORD_SLOPE] THEN
  NLIN_FACTS_TAC []
   [`&1 - (&51 / &100) * s - (&1 / &20) * (c + &609 / &641) <= &1`;
    `&47 / &100 <= &1 - (&51 / &100) * (&609 / &641) + (&1 / &100) * (s + &200 / &641)`] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&609 / &641 - c) *
           (&1 - (&1 - (&51 / &100) * s - (&1 / &20) * (c + &609 / &641)))`;
    `&0 <= (s - &200 / &641) *
           ((&1 - (&51 / &100) * (&609 / &641) + (&1 / &100) * (s + &200 / &641)) -
            &47 / &100)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: edge *)
let C868CSC_EDGE = prove
 (`forall c s. c977cc_normal c s /\
         &1 < (&18 / &25) * c + (&99 / &100) * s /\
         &1 < (&142 / &125) * c + (&1 / &20) * s
         ==> (&53 / &100) * c + (&21 / &20) * s < &1`,
  C868CSC_SETUP [C868CSC_ANGLE] THEN
  C868CSC_USE CCCP_BEFORE [`c:real`; `s:real`; `&299 / &349`; `&180 / &349`;
                           `&53 / &100`; `&21 / &20`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: left *)
let C868CSC_LEFT = prove
 (`forall c s. c977cc_normal c s /\
         &1 < (&18 / &25) * c + (&99 / &100) * s /\
         &1 < (&142 / &125) * c + (&1 / &20) * s
         ==> (&23 / &50) * c pow 2 + (&269 / &250) * c * s - c < --(&1 / &25)`,
  C868CSC_SETUP [C868CSC_ANGLE; C868CSC_REGION] THEN
  C868CSC_USE CCCP_BEFORE [`c:real`; `s:real`; `&299 / &349`; `&180 / &349`;
                           `&23 / &50`; `&269 / &250`] THEN
  NLIN_FACTS_TAC [] [`(&23 / &50) * c + (&269 / &250) * s <= &19 / &20`] THEN
  NLIN_FACTS_TAC [] [`&0 <= c * (&19 / &20 - ((&23 / &50) * c + (&269 / &250) * s))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: top *)
let C868CSC_TOP = prove
 (`forall c s. c977cc_normal c s /\
         &1 < (&18 / &25) * c + (&99 / &100) * s /\
         &1 < (&142 / &125) * c + (&1 / &20) * s
         ==> &1 + (&43 / &500) * c pow 2 + (&13 / &50) * c * s < &59 / &50`,
  C868CSC_SETUP [C868CSC_ANGLE] THEN
  NLIN_FACTS_TAC [] [`&0 <= (&3 * c - &5 * s) * (&5 * c + &3 * s)`] THEN
  SUBGOAL_THEN `(c pow 2 - s pow 2) pow 2 + (&2 * c * s) pow 2 = &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `(c pow 2 - s pow 2) pow 2 + (&2 * c * s) pow 2 =
                 (c pow 2 + s pow 2) pow 2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  C868CSC_USE CCCP_BEFORE [`c pow 2 - s pow 2`; `&2 * c * s`; `&8 / &17`; `&15 / &17`;
                           `&43 / &1000`; `&13 / &100`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: chord *)
let C868CSC_CHORD = prove
 (`forall c s. c977cc_normal c s /\
         &1 < (&18 / &25) * c + (&99 / &100) * s /\
         &1 < (&142 / &125) * c + (&1 / &20) * s
         ==> &543 / &500 < (&443 / &400) * c + (&357 / &400) * s -
                (&10071 / &20000) * c * s - (&1989 / &20000) * c pow 2 +
                (&123 / &8000) * s pow 2`,
  C868CSC_SETUP [C868CSC_ANGLE; C868CSC_REGION; C868CSC_CHORD_SLOPE] THEN
  NLIN_FACTS_TAC []
   [`&443 / &400 - (&10071 / &20000) * s - (&1989 / &20000) * (c + &609 / &641)
       <= &4 / &5`;
    `&2 / &5 <= &357 / &400 - (&10071 / &20000) * (&609 / &641) +
                (&123 / &8000) * (s + &200 / &641)`] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&609 / &641 - c) *
           (&4 / &5 - (&443 / &400 - (&10071 / &20000) * s -
                       (&1989 / &20000) * (c + &609 / &641)))`;
    `&0 <= (s - &200 / &641) *
           ((&357 / &400 - (&10071 / &20000) * (&609 / &641) +
             (&123 / &8000) * (s + &200 / &641)) - &2 / &5)`] THEN
  NLIN_TAC ~deg2:false []);;
