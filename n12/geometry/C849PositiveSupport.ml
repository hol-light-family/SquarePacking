(* ========================================================================= *)
(* Port of Compact/Geometry/C849PositiveSupport.lean                         *)
(* (namespace N12Compact.C849PositiveSupport).                               *)
(* Scalar endgame for the positive-B / upper-U-C sector of 849/851.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

let C849PS_DIV_CANCEL = REAL_FIELD `forall x C. &0 < C ==> C * (x / C) = x`;;

(* Lean: canonical_bounds (private) *)
let C849PS_CANONICAL_BOUNDS = prove
 (`forall C S. &0 < C /\ abs S <= C /\ C pow 2 + S pow 2 = &1
         ==> &7 / &10 <= C /\ C <= &1 /\ abs S <= &71 / &100 /\
             &1 - (&3 / &5) * S pow 2 <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(SPEC `S:real` REAL_ABS_POS) THEN
  ASSUME_TAC(SPEC `S:real` REAL_POW2_ABS) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `S:real`]
   [`abs S pow 2 <= C pow 2`; `C <= &1`; `&7 / &10 <= C`; `abs S <= &71 / &100`;
    `&0 <= (&1 - C) * ((&3 / &5) * C - &2 / &5)`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* Lean: positive_margin (private) *)
let C849PS_POSITIVE_MARGIN = prove
 (`forall C S. &0 < C /\ &0 <= S /\ S <= C /\ C pow 2 + S pow 2 = &1
         ==> &0 < C - &9 / &10 + (&7 / &50) * S pow 2 + S - (&53 / &50) * C * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C849PS_CANONICAL_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= S ==> abs S = S`] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `S - &1 / &2`]
   [`&0 <= (C - (&1 - (&3 / &5) * S pow 2)) * (&1 - (&53 / &50) * S)`;
    `&0 <= (S - &1 / &2) pow 2 * ((S - &1 / &2) + &1 / &2)`] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `&352 * (S - &1 / &2) - &43`]);;

(* Lean: negative_margin (private) *)
let C849PS_NEGATIVE_MARGIN = prove
 (`forall C S. &0 < C /\ S <= &0 /\ abs S <= C /\ C pow 2 + S pow 2 = &1
         ==> &0 < C - &9 / &10 - (&17 / &25) * C * S - (&7 / &500) * S pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C849PS_CANONICAL_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_ARITH `S <= &0 ==> abs S = --S`] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (C - &7 / &10) * --S`; `&0 <= --S * (&71 / &100 + S)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: steep_margin (private) *)
let C849PS_STEEP_MARGIN = prove
 (`forall C S. &0 < C /\ &3 / &5 <= S /\ S <= C /\ C pow 2 + S pow 2 = &1
         ==> &0 < C - &1543 / &1000 + (&783 / &1000) * S pow 2 + S - (&13 / &50) * C * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C849PS_CANONICAL_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_ARITH `&3 / &5 <= S ==> abs S = S`] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `S:real`]
   [`&0 <= (C - (&1 - (&3 / &5) * S pow 2)) * (&1 - (&13 / &50) * S)`;
    `&0 <= (S - &3 / &5) * (S + &3 / &5)`;
    `&0 <= S pow 2 * (S - &3 / &5)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: l_axis_impossible *)
let C849PS_L_AXIS_IMPOSSIBLE = prove
 (`forall c s C S U.
     &0 < c /\ &0 <= s /\ s <= c /\ &0 < C /\ abs S <= C /\
     c pow 2 + s pow 2 = &1 /\ C pow 2 + S pow 2 = &1 /\
     &3 * c / &4 < s /\
     (&0 <= S ==> &1 + S / C + (&187 / &100) * S - ((&19 / &25) * S pow 2) / C <= U) /\
     (S <= &0 ==> &1 - ((&457 / &500) * S pow 2) / C + &2 * S <= U) /\
     (&0 <= c * S - s * C
      ==> U <= C * (&1 + (&543 / &500) * c pow 2 - c + s) +
               S * (&3 + (&543 / &500) * c * s - c - s)) /\
     (c * S - s * C <= &0
      ==> U <= C * (&2 + (&43 / &500) * c pow 2 + c * s / &2 - c - s) +
               S * (&5 / &2 + s pow 2 / &2 + (&43 / &500) * c * s + c - s))
     ==> false`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "hc hs hsc hC hSC unit unitL steep wallPos wallNeg capPos capNeg" THEN
  SUBGOAL_THEN `--C <= S /\ S <= C` STRIP_ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun t -> ASSUME_TAC(UNDISCH(SPECL [t; `C:real`] C849PS_DIV_CANCEL)))
    [`S:real`; `(&19 / &25) * S pow 2`; `(&457 / &500) * S pow 2`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &4 / &5`; SQ_NONNEG `s - &3 / &5`]
   [`&0 < (s - &3 * c / &4) * (s + &3 * c / &4)`; `c <= &4 / &5`; `&3 / &5 <= s`;
    `c - s <= &1 / &5`;
    `&0 <= (&1 / &5 - (c - s)) * (&1 / &5 + (c - s))`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c + s - &7 / &5`; SQ_NONNEG `c - s`;
                  SQ_NONNEG `c + s - &283 / &200`]
   [`&7 / &5 <= c + s`; `c + s <= &283 / &200`; `&0 <= c * s`;
    `&0 <= (c - s) * (&1 - (&543 / &1000) * (c + s))`;
    `&1 + (&543 / &500) * c pow 2 - c + s <= &1543 / &1000`;
    `&0 <= (&283 / &200 - (c + s)) * ((&543 / &1000) * (c + s + &283 / &200) - &1)`;
    `&3 + (&543 / &500) * c * s - c - s <= &213 / &100`;
    `&0 <= (&4 / &5 - c) * (&4 / &5 + c)`;
    `&0 <= (c + s - &7 / &5) * (&13 / &5 - (c + s))`;
    `&2 + (&43 / &500) * c pow 2 + c * s / &2 - c - s <= &9 / &10`;
    `&0 <= (c - s) * (c + s - &7 / &5)`;
    `&5 / &2 + s pow 2 / &2 + (&43 / &500) * c * s + c - s <= &293 / &100`;
    `&0 <= (s - &3 / &5) * (s + &3 / &5)`;
    `&67 / &25 <= &5 / &2 + s pow 2 / &2 + (&43 / &500) * c * s + c - s`] THEN
  ASM_CASES_TAC `&0 <= c * S - s * C` THENL
   [NLIN_FACTS_TAC [] [`&0 < (&4 * s - &3 * c) * C`] THEN
    SUBGOAL_THEN `&3 * C < &4 * S` ASSUME_TAC THENL
     [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
      NLIN_FACTS_TAC [] [`&0 <= c * (&3 * C - &4 * S)`] THEN NLIN_TAC ~deg2:false [];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "wallPos" (fun th -> MP_TAC(MATCH_MP th (ASSUME `&0 <= S`))) THEN
    USE_THEN "capPos" (fun th -> MP_TAC(MATCH_MP th (ASSUME `&0 <= c * S - s * C`))) THEN
    REPEAT DISCH_TAC THEN
    NLIN_FACTS_TAC [SQ_NONNEG `S - &3 / &5`]
     [`&0 < (&4 * S - &3 * C) * (&4 * S + &3 * C)`; `&3 / &5 <= S`;
      `C * (&1 + (&543 / &500) * c pow 2 - c + s) <= C * (&1543 / &1000)`;
      `S * (&3 + (&543 / &500) * c * s - c - s) <= S * (&213 / &100)`;
      `U <= (&1543 / &1000) * C + (&213 / &100) * S`;
      `&0 <= C * (U - (&1 + S / C + (&187 / &100) * S - ((&19 / &25) * S pow 2) / C))`;
      `&0 <= C * ((&1543 / &1000) * C + (&213 / &100) * S - U)`] THEN
    MP_TAC(SPECL [`C:real`; `S:real`] C849PS_STEEP_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
  SUBGOAL_THEN `c * S - s * C <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "capNeg" (fun th -> MP_TAC(MATCH_MP th (ASSUME `c * S - s * C <= &0`))) THEN
  DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`C * (&2 + (&43 / &500) * c pow 2 + c * s / &2 - c - s) <= C * (&9 / &10)`] THEN
  ASM_CASES_TAC `&0 <= S` THENL
   [USE_THEN "wallPos" (fun th -> MP_TAC(MATCH_MP th (ASSUME `&0 <= S`))) THEN
    DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`S * (&5 / &2 + s pow 2 / &2 + (&43 / &500) * c * s + c - s) <= S * (&293 / &100)`;
      `U <= (&9 / &10) * C + (&293 / &100) * S`;
      `&0 <= C * (U - (&1 + S / C + (&187 / &100) * S - ((&19 / &25) * S pow 2) / C))`;
      `&0 <= C * ((&9 / &10) * C + (&293 / &100) * S - U)`] THEN
    MP_TAC(SPECL [`C:real`; `S:real`] C849PS_POSITIVE_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    NLIN_TAC ~deg2:false [];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN `S <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "wallNeg" (fun th -> MP_TAC(MATCH_MP th (ASSUME `S <= &0`))) THEN
    DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`S * (&5 / &2 + s pow 2 / &2 + (&43 / &500) * c * s + c - s) <= S * (&67 / &25)`;
      `U <= (&9 / &10) * C + (&67 / &25) * S`;
      `&0 <= C * (U - (&1 - ((&457 / &500) * S pow 2) / C + &2 * S))`;
      `&0 <= C * ((&9 / &10) * C + (&67 / &25) * S - U)`] THEN
    MP_TAC(SPECL [`C:real`; `S:real`] C849PS_NEGATIVE_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    NLIN_TAC ~deg2:false []]);;
