(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallLowerCorner.lean                      *)
(* lower is ABT_lower.                                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FullAuxWallEscape.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: scalar *)
let FAWLC_SCALAR = prove
 (`forall c s e v. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ &4 * s <= c /\
     e < (&13 / &50) * s /\ v < c - &1 - (&2 / &5) * s
     ==> s * e + c * v < &0 /\ (c + s) * e + (c - s) * v < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
   [`c <= &1`; `&0 <= (c - &4 * s) * (c + &4 * s)`; `&24 / &25 <= c`;
    `&0 <= (&1 - c) * (c - &1 / &2)`; `&1 - c <= (&2 / &3) * s pow 2`; `&0 < c * s`;
    `s * e < s * ((&13 / &50) * s)`; `c * v < c * (c - &1 - (&2 / &5) * s)`;
    `s * e + c * v < &0`;
    `(c + s) * e < (c + s) * ((&13 / &50) * s)`;
    `(c - s) * v < (c - s) * (c - &1 - (&2 / &5) * s)`;
    `&0 <= s * (c - &4 * s)`; `&0 <= s * (c - &24 / &25)`] THEN
  ASM_REWRITE_TAC[] THEN NLIN_TAC [SQ_NONNEG `s:real`]);;

(* Lean: projection *)
let FAWLC_PROJECTION = prove
 (`forall c s e v C S. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ &4 * s <= c /\
     e < (&13 / &50) * s /\ v < c - &1 - (&2 / &5) * s /\
     &0 < C /\ &0 <= S /\ S <= C
     ==> (c * S + s * C) * e + (c * C - s * S) * v < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `e:real`; `v:real`] FAWLC_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c * S + s * C) * e + (c * C - s * S) * v =
                S * ((c + s) * e + (c - s) * v) + (C - S) * (s * e + c * v)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 < S` THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `S = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: opposite_v_impossible *)
let FAWLC_OPPOSITE_V_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cD sD uD vD aD S.
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     &1 < aA /\ &0 < cA /\ &0 < sA /\ &4 * sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     sD = --S /\ &0 < cD /\ &0 <= S /\ S <= cD /\
     linside cD sD uD vD aD (&2) (&2) /\
     vD + aD <= ABT_lower cA sA uA vA aA (--sD) cD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sD = --S` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cA sA uA vA aA (&2) (&113 / &50)`; `linside cD (--S) uD vD aD (&2) (&2)`] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA - &2 * (cA + sA)`; `vA - &2 * (cA - sA)`;
                `cD:real`; `S:real`] FAWLC_PROJECTION) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
                  DISCH_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= cA * S + sA * cD`; `&0 <= cA * cD - sA * S`] THEN
  SUBGOAL_THEN `ABT_lower cA sA uA vA aA S cD =
                (cA * S + sA * cD) * uA + (cA * cD - sA * S) * vA` ASSUME_TAC THENL
   [REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
    SUBGOAL_THEN `abs(S * cA + cD * sA) = cA * S + sA * cD /\
                  abs(--S * sA + cD * cA) = cA * cD - sA * S`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(cA * S + sA * cD) * uA + (cA * cD - sA * S) * vA - &2 * (S + cD) =
                (cA * S + sA * cD) * (uA - &2 * (cA + sA)) +
                (cA * cD - sA * S) * (vA - &2 * (cA - sA))` ASSUME_TAC THENL
   [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_lower cA sA uA vA aA S cD =
                (cA * S + sA * cD) * uA + (cA * cD - sA * S) * vA`]) THEN
  RASM_ARITH_TAC);;
