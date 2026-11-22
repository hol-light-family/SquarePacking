(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeBottomCentralAxis.lean (Jatloe).          *)
(* A steep negative bottom singleton cannot pass its upper transverse face   *)
(* through a negative bottom wall below the negative central neighbour.      *)
(* Normal: c977cc_normal; boundary: c977cc_boundary; upper/lower: ABT_*;     *)
(* a square D with D.s = -r is written with the hypothesis sD = --r;         *)
(* upper/lower_negative_pos/nonpos: C977NCO_UPPER/LOWER_NEGATIVE_POS/NONPOS. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralNegativeBottomAxes.ml";;
needs "n12/geometry/OwnedWestBottomAngle.ml";;

(* Lean: support_bound *)
let NBCA_SUPPORT_BOUND = prove
 (`forall cD sD uD vD aD cB sB (uB:real) vB aB r t p s.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sD = --r /\ c977cc_normal cD r /\ c977cc_normal cB t /\ c977cc_normal p s /\
     &47 / &100 < s /\ t <= &3 / &10 /\ aD = aB /\ &1 <= aB /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     ABT_upper cD sD uD vD aD t cB <= vB /\
     vB + aB <= &2 * cB + &3 * t
     ==> ABT_lower cD sD uD vD aD s p <= &2 * s + (&3 / &5) * p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cD /\ &0 < cB /\ &0 <= p` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `&3 / &10 - t` `&3 / &10 + t` THEN
  SUBGOAL_THEN `&9 / &10 <= cB` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCT_PROD_TAC `&9 / &10 - cB` `&9 / &10 + cB` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `t:real` `r:real` THEN PCT_PRODLT_TAC `cB:real` `cD:real` THEN
  PCT_PROD_TAC `s:real` `r:real` THEN PCT_PROD_TAC `p:real` `cD:real` THEN
  PCT_PROD_TAC `s:real` `cB - &9 / &10` THEN PCT_PROD_TAC `t:real` `&1 - p` THEN
  SUBGOAL_THEN `&0 < (t * r + cB * cD) /\ &0 <= (s * r + p * cD) /\ &0 <= (s * cB - p * t)` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(t * cD - cB * r) * uD + (t * r + cB * cD) * (vD + aB) <= ABT_upper cD (--r) uD vD aB t cB`
  ASSUME_TAC THENL
  [ASM_CASES_TAC `&0 <= (t * cD - cB * r)` THENL
   [MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`; `r:real`;
                  `t:real`; `cB:real`] C977NCO_UPPER_NEGATIVE_POS) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    PCT_PROD_TAC `(t * cD - cB * r)` `aB:real` THEN RASM_ARITH_TAC;
    MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`; `r:real`;
                  `t:real`; `cB:real`] C977NCO_UPPER_NEGATIVE_NONPOS) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    RASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cD (--r) uD vD aB s p <= (s * cD - p * r) * uD + (s * r + p * cD) * vD`
  ASSUME_TAC THENL
  [ASM_CASES_TAC `&0 <= (s * cD - p * r)` THENL
   [MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`; `r:real`;
                  `s:real`; `p:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`; `r:real`;
                  `s:real`; `p:real`] C977NCO_LOWER_NEGATIVE_NONPOS) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    PCT_PROD_TAC `--(s * cD - p * r)` `aB:real` THEN RASM_ARITH_TAC]; ALL_TAC] THEN
  UNDISCH_TAC `linside cD (--r) uD vD aB (&2) (&457 / &500)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  PCT_PROD_TAC `(s * r + p * cD)` `vB - ABT_upper cD (--r) uD vD aB t cB` THEN
  PCT_PROD_TAC `(s * r + p * cD)` `ABT_upper cD (--r) uD vD aB t cB - ((t * cD - cB * r) * uD + (t * r + cB * cD) * (vD + aB))` THEN
  PCT_PROD_TAC `(s * r + p * cD)` `(&2 * cB + &3 * t) - (vB + aB)` THEN
  PCT_PROD_TAC `(t * r + cB * cD)` `((s * cD - p * r) * uD + (s * r + p * cD) * vD) - ABT_lower cD (--r) uD vD aB s p` THEN
  PCT_PROD_TAC `(s * cB - p * t)` `&2 * cD - (&457 / &500) * r - uD` THEN
  PCT_PROD_TAC `(s * r + p * cD)` `(t * r + cB * cD)` THEN
  PCT_PROD_TAC `(s * r + p * cD) + (s * r + p * cD) * (t * r + cB * cD)` `aB - &1` THEN
  SUBGOAL_THEN `(t * r + cB * cD) * ((s * cD - p * r) * uD + (s * r + p * cD) * vD) =
                (s * cB - p * t) * uD + (s * r + p * cD) * ((t * cD - cB * r) * uD + (t * r + cB * cD) * (vD + aB)) - (s * r + p * cD) * (t * r + cB * cD) * aB`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(t * r + cB * cD) * ABT_lower cD (--r) uD vD aB s p <=
                (s * cB - p * t) * (&2 * cD - (&457 / &500) * r) + (s * r + p * cD) * (&2 * cB + &3 * t - &1 - (t * r + cB * cD))`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `&1 - cB` `&543 / &500 - cD` THEN
  PCT_PROD_TAC `&1 - cB` `&7 / &5 - cD` THEN
  SUBGOAL_THEN `cB * (&543 / &500 - cD) + t * (&1 - r) - &1 <= &0 /\
                cB * (&7 / &5 - cD) + t - &1 <= &0 /\ &157 / &500 - cD <= &0`
  STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `s * r` `--(cB * (&543 / &500 - cD) + t * (&1 - r) - &1)` THEN
  PCT_PROD_TAC `p * cD` `--(cB * (&7 / &5 - cD) + t - &1)` THEN
  PCT_PROD_TAC `p:real` `t:real` THEN PCT_PROD_TAC `p * t` `r:real` THEN
  PCT_PROD_TAC `(p * t) * r` `--(&157 / &500 - cD)` THEN
  SUBGOAL_THEN
   `(s * cB - p * t) * (&2 * cD - (&457 / &500) * r) + (s * r + p * cD) * (&2 * cB + &3 * t - &1 - (t * r + cB * cD)) -
    (t * r + cB * cD) * (&2 * s + (&3 / &5) * p) =
    s * r * (cB * (&543 / &500 - cD) + t * (&1 - r) - &1) +
    p * cD * (cB * (&7 / &5 - cD) + t - &1) + p * t * r * (&157 / &500 - cD)`
  ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(t * r + cB * cD) * (ABT_lower cD (--r) uD vD aB s p - (&2 * s + (&3 / &5) * p)) <= &0`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  PCT_PRODLT_TAC `(t * r + cB * cD)` `ABT_lower cD (--r) uD vD aB s p - (&2 * s + (&3 / &5) * p)` THEN
  RASM_ARITH_TAC);;

(* Lean: boundary_margin *)
let NBCA_BOUNDARY_MARGIN = prove
 (`forall p s. c977cc_normal p s ==> &2 * s + (&3 / &5) * p < c977cc_boundary p s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s <= &5 / &7` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PRODLT_TAC `&1 - s` `p + (&2 / &5) * s - &3 / &5` THEN
  MP_TAC(SPECL [`p:real`; `s:real`] OWBA_BOUNDARY_EXACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p * (c977cc_boundary p s - (&2 * s + (&3 / &5) * p)) =
                (&1 - s) * (p + (&2 / &5) * s - &3 / &5)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:real`; `c977cc_boundary p s - (&2 * s + (&3 / &5) * p)`]
    PCT_POS_BY_POS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: impossible *)
let NBCA_IMPOSSIBLE = prove
 (`forall cO sO (uO:real) vO aO cD sD uD vD aD cB sB (uB:real) vB aB s r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cO s /\ c977cc_normal cD r /\ c977cc_normal cB t /\
     sD = --r /\ aD = aB /\ &1 <= aB /\ &47 / &100 < s /\ t <= &3 / &10 /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     c977cc_boundary cO s < vO + aO /\
     vO + aO <= ABT_lower cD sD uD vD aD s cO /\
     ABT_upper cD sD uD vD aD t cB <= vB /\
     vB + aB <= &2 * cB + &3 * t
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `r:real`; `t:real`; `cO:real`; `s:real`] NBCA_SUPPORT_BOUND) THEN
  MP_TAC(SPECL [`cO:real`; `s:real`] NBCA_BOUNDARY_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;
