(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976NegativeTop/TopScalars.lean     *)
(* (namespace N12Compact.Completion.OtherCases.C976NegativeTop).            *)
(* Section 4 scalar arguments of C976-NEGATIVE-NE-TOP-ENDING.               *)
(* wall_delta: C976NTQ_WALL_DELTA; CanonicalProjection.after: CCCP_AFTER;   *)
(* CanonicalScalars.bounds: CCCS_BOUNDS.  The endpoint witness 3/sqrt 13,   *)
(* 2/sqrt 13 is written 3 sqrt 13 / 13, 2 sqrt 13 / 13.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_QuadrantScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let C976NTT_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [FIRST [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
     REPEAT CONJ_TAC THEN TRY (MATCH_ACCEPT_TAC REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) tms;;

(* Lean: endpoint (private) *)
let C976NTT_ENDPOINT = prove
 (`exists c0 s0. &0 < c0 /\ &0 < s0 /\ c0 pow 2 + s0 pow 2 = &1 /\ s0 = (&2 / &3) * c0 /\
           (&9 / &10) * c0 + (&11 / &25) * s0 < &1 /\
           &0 < (&5 / &3) * c0 - s0 / &3 - &209 / &150 + (&6 / &5) * s0 pow 2 -
                (&11 / &30) * c0 * s0`,
  MP_TAC(SPEC `&13` SQRT_POW_2) THEN MP_TAC(SPEC `&13` SQRT_POS_LT) THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; ARITH] THEN
  SPEC_TAC(`sqrt(&13)`,`r:real`) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&179 / &50 < r /\ r < &181 / &50` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  EXISTS_TAC `&3 * r / &13` THEN EXISTS_TAC `&2 * r / &13` THEN
  UNDISCH_TAC `r pow 2 = &13` THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: high_projection (private) *)
let C976NTT_HIGH_PROJECTION = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ (&2 / &3) * c <= s
         ==> (&9 / &10) * c + (&11 / &25) * s < &1`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC C976NTT_ENDPOINT THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `c0:real`; `s0:real`; `&9 / &10`; `&11 / &25`]
    CCCP_AFTER) THEN
  C976NTT_PROD_TAC [`&0 <= c0 * (s - (&2 / &3) * c)`] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Lean: outer_low (private) *)
let C976NTT_OUTER_LOW = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ s <= (&2 / &3) * c
         ==> &0 < (&5 / &3) * c - s / &3 - &209 / &150 + (&6 / &5) * s pow 2 -
                  (&11 / &30) * c * s`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC C976NTT_ENDPOINT THEN
  SUBGOAL_THEN `c <= &1 /\ c0 <= &1` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN CONJ_TAC THEN
    NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `s0:real`]; ALL_TAC] THEN
  C976NTT_PROD_TAC [`&0 <= c0 * ((&2 / &3) * c - s)`] THEN
  SUBGOAL_THEN `c0 * s <= s0 * c` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s <= s0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c < c0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C976NTT_PROD_TAC [`&0 <= (c - c0) * (c + c0)`; `&0 < (s - s0) * (s + s0)`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    C976NTT_PROD_TAC [`&0 < c0 * (s - s0)`; `&0 < s0 * (c0 - c)`] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `uu = c + c0` THEN ABBREV_TAC `vv = s + s0` THEN
  SUBGOAL_THEN `&0 < uu /\ &0 <= vv /\ uu <= &2 /\ vv <= (&2 / &3) * uu` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["uu"; "vv"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = vv / uu` THEN
  SUBGOAL_THEN `t * uu = vv` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN UNDISCH_TAC `&0 < uu` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t /\ t <= &2 / &3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  C976NTT_PROD_TAC [`&0 <= (&2 / &3 - t) * (&11 * t + &88 / &3)`] THEN
  SUBGOAL_THEN `&11 * t pow 2 + &22 * t - &21 <= --(&13 / &9)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &50 * t + &10 - (uu / &2) * (&72 * t - &11 + &11 * t pow 2)`
    ASSUME_TAC THENL
   [ASM_CASES_TAC `&72 * t - &11 + &11 * t pow 2 <= &0` THENL
     [C976NTT_PROD_TAC [`&0 <= (uu / &2) * --(&72 * t - &11 + &11 * t pow 2)`] THEN
      ASM_REAL_ARITH_TAC;
      C976NTT_PROD_TAC [`&0 <= (&1 - uu / &2) * (&72 * t - &11 + &11 * t pow 2)`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `A = &5 / &3 - (&11 / &60) * vv` THEN
  ABBREV_TAC `B = --(&1 / &3) + (&6 / &5) * vv - (&11 / &60) * uu` THEN
  SUBGOAL_THEN `&30 * (A * vv - B * uu) =
                uu * (&50 * t + &10 - (uu / &2) * (&72 * t - &11 + &11 * t pow 2))`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN UNDISCH_TAC `t * uu = vv` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C976NTT_PROD_TAC
   [`&0 <= uu * (&50 * t + &10 - (uu / &2) * (&72 * t - &11 + &11 * t pow 2))`] THEN
  SUBGOAL_THEN `&0 <= A * vv - B * uu` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `uu * (((&5 / &3) * c - s / &3 - &209 / &150 + (&6 / &5) * s pow 2 - (&11 / &30) * c * s) -
          ((&5 / &3) * c0 - s0 / &3 - &209 / &150 + (&6 / &5) * s0 pow 2 -
           (&11 / &30) * c0 * s0)) =
    (s0 - s) * (A * vv - B * uu)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[GSYM(ASSUME `c + c0 = uu`); GSYM(ASSUME `s + s0 = vv`)] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `c0 pow 2 + s0 pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C976NTT_PROD_TAC [`&0 <= (s0 - s) * (A * vv - B * uu)`] THEN
  SUBGOAL_THEN
   `&0 <= ((&5 / &3) * c - s / &3 - &209 / &150 + (&6 / &5) * s pow 2 - (&11 / &30) * c * s) -
          ((&5 / &3) * c0 - s0 / &3 - &209 / &150 + (&6 / &5) * s0 pow 2 -
           (&11 / &30) * c0 * s0)` MP_TAC THENL
   [MP_TAC(ISPECL [`uu:real`;
      `((&5 / &3) * c - s / &3 - &209 / &150 + (&6 / &5) * s pow 2 - (&11 / &30) * c * s) -
       ((&5 / &3) * c0 - s0 / &3 - &209 / &150 + (&6 / &5) * s0 pow 2 -
        (&11 / &30) * c0 * s0)`] (CONJUNCT1 REAL_LE_MUL_EQ)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Lean: outer_coefficients (private) *)
let C976NTT_OUTER_COEFFICIENTS = prove
 (`forall c s. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> &0 < c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C976NTT_PROD_TAC [`&0 < c * c`; `&0 <= (c - s) * (c - s)`; `&0 <= s * s`] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
  ASM_REAL_ARITH_TAC);;

let C976NTT_SZERO_TAC A =
  SUBGOAL_THEN `C = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC A THEN REAL_ARITH_TAC;;

(* Lean: top_outer_margin *)
let C976NTT_TOP_OUTER_MARGIN = prove
 (`forall c s C S. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
             &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\ (&2 / &3) * S <= C /\
             &0 <= c * C - s * S
     ==> &0 < (c * S + s * C) * (&1 - c - (&11 / &25) * s) +
              (c * C - s * S) * (&1 - (&37 / &50) * c) +
              (&1 - (&1 - S) / C - (&18 / &25) * S)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C976NTT_OUTER_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c * S + s * C) * (&1 - c - (&11 / &25) * s) +
                (c * C - s * S) * (&1 - (&37 / &50) * c) =
                C * (c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s) +
                S * (c - s - c pow 2 + (&3 / &10) * c * s)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `S = &0` THENL
   [C976NTT_SZERO_TAC `&0 < c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s`;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C976NTQ_WALL_DELTA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `s <= (&2 / &3) * c` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`] C976NTT_OUTER_LOW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (&2 / &3) * (c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s) +
                       (c - s - c pow 2 + (&3 / &10) * c * s) + &1 / &10` ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    C976NTT_PROD_TAC
     [`&0 <= (C - (&2 / &3) * S) *
             (c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s)`;
      `&0 < S * ((&2 / &3) * (c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s) +
                 (c - s - c pow 2 + (&3 / &10) * c * s) + &1 / &10)`] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`c:real`; `s:real`] C976NTT_HIGH_PROJECTION) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    C976NTT_PROD_TAC
     [`&0 <= (c * C - s * S) *
             (c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s)`;
      `&0 < S * (&1 - (&9 / &10) * c - (&11 / &25) * s)`] THEN
    SUBGOAL_THEN
     `c * (C * (c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s) +
           S * (c - s - c pow 2 + (&3 / &10) * c * s) + (&1 / &10) * S) =
      (c * C - s * S) * (c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s) +
      S * (&1 - (&9 / &10) * c - (&11 / &25) * s)` ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < C * (c + s - (&37 / &50) * c pow 2 - (&11 / &25) * s pow 2 - c * s) +
           S * (c - s - c pow 2 + (&3 / &10) * c * s) + (&1 / &10) * S` MP_TAC THENL
     [MATCH_MP_TAC(MESON[REAL_LT_MUL_EQ] `forall c x. &0 < c /\ &0 < c * x ==> &0 < x`) THEN
      EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* Lean: top_mixed_margin *)
let C976NTT_TOP_MIXED_MARGIN = prove
 (`forall c s C S. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
             &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\ (&2 / &3) * S <= C /\
             s < (&13 / &25) * c
     ==> &0 < (c * S + s * C) * (&1 - c - (&11 / &25) * s) +
              (c * C - s * S) * (&1 + (&1 / &2) * s - c) +
              (&1 - (&1 - S) / C - (&18 / &25) * S)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C976NTT_PROD_TAC [`&0 < c * s`; `&0 <= s * s`;
                    `&0 <= (&13 / &25 * c - s) * (&13 / &25 * c + s)`] THEN
  SUBGOAL_THEN `&0 < c + s - c pow 2 - (&11 / &25) * s pow 2 - (&1 / &2) * c * s`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &8 <= c /\ s <= &1 / &2 /\ s * s <= &1 / &4` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    NLIN_FACTS_TAC [] [`&7 / &8 <= c`; `s <= &1 / &2`; `s * s <= &1 / &4`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C976NTT_PROD_TAC [`&0 <= (s * s) * (&8 / &15 * (&1 + c) - &1)`] THEN
  SUBGOAL_THEN `&0 <= c - &1 + &8 / &15 * s * s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&1 + c`; `c - &1 + &8 / &15 * s * s`] (CONJUNCT1 REAL_LE_MUL_EQ)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    UNDISCH_TAC `&0 <= (s * s) * (&8 / &15 * (&1 + c) - &1)` THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  C976NTT_PROD_TAC [`&0 <= s * (&17 * c / &75 - &1 / &3 + &27 / &200)`] THEN
  SUBGOAL_THEN
   `--(&257 / &3600) <=
    (&2 / &3) * (c + s - c pow 2 - (&11 / &25) * s pow 2 - (&1 / &2) * c * s) +
    (c - s - c pow 2 - (&1 / &2) * s pow 2 + (&14 / &25) * c * s)` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c * S + s * C) * (&1 - c - (&11 / &25) * s) +
                (c * C - s * S) * (&1 + (&1 / &2) * s - c) =
                C * (c + s - c pow 2 - (&11 / &25) * s pow 2 - (&1 / &2) * c * s) +
                S * (c - s - c pow 2 - (&1 / &2) * s pow 2 + (&14 / &25) * c * s)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `S = &0` THENL
   [C976NTT_SZERO_TAC `&0 < c + s - c pow 2 - (&11 / &25) * s pow 2 - (&1 / &2) * c * s`;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C976NTQ_WALL_DELTA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C976NTT_PROD_TAC
   [`&0 <= (C - (&2 / &3) * S) *
           (c + s - c pow 2 - (&11 / &25) * s pow 2 - (&1 / &2) * c * s)`;
    `&0 <= S * ((&2 / &3) * (c + s - c pow 2 - (&11 / &25) * s pow 2 - (&1 / &2) * c * s) +
                (c - s - c pow 2 - (&1 / &2) * s pow 2 + (&14 / &25) * c * s) +
                &257 / &3600)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: top_negative_margin *)
let C976NTT_TOP_NEGATIVE_MARGIN = prove
 (`forall c s C S. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\
             &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\ (&2 / &3) * S <= C /\
             c * C - s * S < &0
     ==> &0 < (c * S + s * C) * (&1 - c - (&11 / &25) * s) +
              (&1 - (&1 - S) / C - (&18 / &25) * S)`,
  REPEAT STRIP_TAC THEN
  C976NTT_PROD_TAC [`&0 < c * C`] THEN
  SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `S = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C976NTT_PROD_TAC [`&0 <= c * (C - (&2 / &3) * S)`] THEN
  SUBGOAL_THEN `(&2 / &3) * c <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C976NTT_PROD_TAC [`&0 < S * ((&2 / &3) * c - s)`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C976NTT_HIGH_PROJECTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C976NTT_PROD_TAC [`&0 < c * S`; `&0 < s * C`; `&0 < s * S`] THEN
  SUBGOAL_THEN `c < S` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c * C - s * S) * (c * C + s * S) = c pow 2 - S pow 2` ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < --(c * C - s * S) * (c * C + s * S)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C976NTT_PROD_TAC [`&0 <= (c - S) * (c + S)`] THEN
    UNDISCH_TAC `(c * C - s * S) * (c * C + s * S) = c pow 2 - S pow 2` THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = c * S + s * C` THEN
  SUBGOAL_THEN `k <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c * C - s * S) pow 2 + k pow 2 = &1` MP_TAC THENL
     [EXPAND_TAC "k" THEN
      UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    SPEC_TAC(`c * C - s * S`,`d:real`) THEN GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
    DISCH_TAC THEN NLIN_TAC [SQ_NONNEG `d:real`; SQ_NONNEG `k - &1`]; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C976NTQ_WALL_DELTA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= &1 - c - (&11 / &25) * s` THENL
   [C976NTT_PROD_TAC [`&0 <= k * (&1 - c - (&11 / &25) * s)`] THEN ASM_REAL_ARITH_TAC;
    C976NTT_PROD_TAC [`&0 <= (&1 - k) * --(&1 - c - (&11 / &25) * s)`] THEN
    ASM_REAL_ARITH_TAC]);;
