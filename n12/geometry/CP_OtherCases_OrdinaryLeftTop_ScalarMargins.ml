(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/ScalarMargins.lean  *)
(* (N12Compact.Completion.OtherCases.OrdinaryLeftTop.ScalarMargins).         *)
(* Exact projection margins used in Theorem 1 of                             *)
(* ORDINARY-LEFT-TOP-OBSTRUCTION.md.  Purely scalar.  Tag OLTSM_.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: lt_one_of_square (private) *)
let OLTSM_LT_ONE_OF_SQUARE = prove
 (`forall z. z pow 2 < &1 ==> z < &1`,
  GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_TAC []);;

(* Lean: endpoint (private) *)
let OLTSM_ENDPOINT = prove
 (`forall c s m n k z. c pow 2 + s pow 2 = &1 /\
     z <= k * (m * c + n * s) /\
     k pow 2 * (m pow 2 + n pow 2) < &1
     ==> z < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k * (m * c + n * s)) pow 2 < &1` MP_TAC THENL
   [SUBGOAL_THEN `(k * (m * c + n * s)) pow 2 + (k * (n * c - m * s)) pow 2 =
                  k pow 2 * (m pow 2 + n pow 2)` MP_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
      MP_TAC(SPEC `k * (n * c - m * s)` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o MATCH_MP OLTSM_LT_ONE_OF_SQUARE) THEN ASM_REAL_ARITH_TAC]);;

let OLTSM_ENDPOINT_TAC m n k =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC OLTSM_ENDPOINT THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; m; n; k] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REAL_ARITH_TAC;;

(* Lean: threeTenths *)
let OLTSM_THREETENTHS = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> &3 / &10 * c + s < &1`,
  OLTSM_ENDPOINT_TAC `&1` `&1` `&13 / &20`);;

(* Lean: sixHundredths *)
let OLTSM_SIXHUNDREDTHS = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> &3 / &50 * c + s < &1`,
  OLTSM_ENDPOINT_TAC `&1` `&1` `&53 / &100`);;

(* Lean: twentySevenOneOhFour *)
let OLTSM_TWENTYSEVENONEOHFOUR = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> &27 / &100 * c + &26 / &25 * s < &1`,
  OLTSM_ENDPOINT_TAC `&1` `&1` `&131 / &200`);;

(* Lean: seventeenOneOhFour *)
let OLTSM_SEVENTEENONEOHFOUR = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> &17 / &100 * c + &26 / &25 * s < &1`,
  OLTSM_ENDPOINT_TAC `&1` `&1` `&121 / &200`);;

(* Lean: smallSine *)
let OLTSM_SMALLSINE = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &3 / &7 * c <= s
         ==> c + &43 / &500 * s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CCCS_C_SMALL_SINE THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: halfBeforeTwoThirds *)
let OLTSM_HALFBEFORETWOTHIRDS = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         s <= &2 / &3 * c
         ==> &1 / &2 * c + s < &1`,
  OLTSM_ENDPOINT_TAC `&3` `&2` `&7 / &26`);;

(* Lean: lowTwoThirds *)
let OLTSM_LOWTWOTHIRDS = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         s <= &2 / &3 * c
         ==> &263 / &500 * c + s < &1`,
  OLTSM_ENDPOINT_TAC `&3` `&2` `&1789 / &6500`);;

(* Lean: lowSixth *)
let OLTSM_LOWSIXTH = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         s <= c / &6
         ==> &413 / &500 * c + s < &1`,
  OLTSM_ENDPOINT_TAC `&6` `&1` `&1489 / &9250`);;

(* Lean: sixthSlopeSine *)
let OLTSM_SIXTHSLOPESINE = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         c / &6 < s
         ==> c + &3 / &50 * s < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2491 / &2500 * s - &3 / &25 * c` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * (&2491 / &2500 * s - &3 / &25 * c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: oneOhFourSeventeen *)
let OLTSM_ONEOHFOURSEVENTEEN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &2 / &3 * c <= s
         ==> &26 / &25 * c + &17 / &100 * s < &1`,
  OLTSM_ENDPOINT_TAC `&3` `&2` `&173 / &650`);;

(* Lean: pointUpperV *)
let OLTSM_POINTUPPERV = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &2 / &3 * c <= s
         ==> &26 / &25 * c - &1 / &100 * s < &1`,
  OLTSM_ENDPOINT_TAC `&3` `&2` `&31 / &130`);;

(* Lean: highEightElevenths *)
let OLTSM_HIGHEIGHTELEVENTHS = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &8 / &11 * c <= s
         ==> &26 / &25 * c + &27 / &100 * s < &1`,
  OLTSM_ENDPOINT_TAC `&11` `&8` `&68 / &925`);;

(* Lean: pointUpperU *)
let OLTSM_POINTUPPERU = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         s <= &8 / &11 * c
         ==> &243 / &500 * c + s < &1`,
  OLTSM_ENDPOINT_TAC `&11` `&8` `&6673 / &92500`);;

(* Lean: originUpper *)
let OLTSM_ORIGINUPPER = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         s <= &8 / &11 * c
         ==> &11 / &25 * c + s < &1`,
  OLTSM_ENDPOINT_TAC `&11` `&8` `&321 / &4625`);;
