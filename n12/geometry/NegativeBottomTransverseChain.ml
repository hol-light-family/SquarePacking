(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeBottomTransverseChain.lean (Jatloe).      *)
(* One complete selector of the negative bottom-wall chain is impossible.    *)
(* Normal: c977cc_normal; upper: ABT_upper; D.s = -r written sD = --r;       *)
(* cosine_order: C977CSB_COSINE_ORDER; upper_in_bands specialisations:       *)
(* C977NCO_UPPER_NEGATIVE_POS/NONPOS.                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralNegativeBottomAxes.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

(* Lean: first_margin (private) *)
let NBTC_FIRST_MARGIN = prove
 (`forall c t d r. c977cc_normal c t /\ c977cc_normal d r /\ t <= &3 / &10
     ==> &0 < &1 + c * (d - &31 / &25 + (&77 / &500) * r pow 2 - (&13 / &100) * d * r) +
              t * (r - &1 - (&13 / &100) * r pow 2 - (&77 / &500) * d * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `d * r <= &1 / &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `d - r:real`]; ALL_TAC] THEN
  MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  PCT_PROD_TAC `r:real` `&1 - (&13 / &100) * r - (&77 / &500) * d` THEN
  PCT_PROD_TAC `c:real`
    `(d - &31 / &25 + (&77 / &500) * r pow 2 - (&13 / &100) * d * r) + &121 / &200` THEN
  PCT_PROD_TAC `t:real` `(r - &1 - (&13 / &100) * r pow 2 - (&77 / &500) * d * r) + &1` THEN
  RASM_ARITH_TAC);;

(* Lean: last_margin (private) *)
let NBTC_LAST_MARGIN = prove
 (`forall c t d r. c977cc_normal c t /\ c977cc_normal d r /\ t <= &3 / &10 /\ r <= t
     ==> &0 < &1 + c * (d - &31 / &25 + (&6 / &25) * r pow 2 - (&99 / &100) * d * r) +
              t * (r - &7 / &50 - (&99 / &100) * r pow 2 - (&6 / &25) * d * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `r <= &3 / &10` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `&3 / &10 - r` `&3 / &10 + r` THEN
  SUBGOAL_THEN `&9 / &10 <= d` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCT_PROD_TAC `&9 / &10 - d` `&9 / &10 + d` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `r:real` `&1 - d` THEN
  SUBGOAL_THEN `d * r <= &3 / &10` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  PCT_PROD_TAC `r:real` `&1 - (&99 / &100) * r - (&6 / &25) * d` THEN
  PCT_PROD_TAC `c:real`
    `(d - &31 / &25 + (&6 / &25) * r pow 2 - (&99 / &100) * d * r) + &637 / &1000` THEN
  PCT_PROD_TAC `t:real`
    `(r - &7 / &50 - (&99 / &100) * r pow 2 - (&6 / &25) * d * r) + &7 / &50` THEN
  RASM_ARITH_TAC);;

(* Lean: impossible *)
let NBTC_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD cB sB (uB:real) vB aB r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cD r /\ c977cc_normal cB t /\ sD = --r /\
     aD = aB /\ &1 < aB /\ t <= &3 / &10 /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&143 / &50) (&1) /\
     ABT_upper cO sO uO vO aO r cD <= vD /\
     ABT_upper cD sD uD vD aD t cB <= vB /\
     vB + aB <= &2 * cB + &3 * t
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  PCT_NORMAL_TAC THEN
  ABT_SB_TAC [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`]
    `&187 / &100` `&19 / &25` `r:real` `cD:real` THEN
  SUBGOAL_THEN `(&187 / &100) * r + (&19 / &25) * cD < vD` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `linside cD (--r) uD vD aB (&2) (&457 / &500)` THEN
  UNDISCH_TAC `linside cD (--r) uD vD aB (&143 / &50) (&1)` THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < cD /\ &0 < cB` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `t:real` `r:real` THEN PCT_PRODLT_TAC `cB:real` `cD:real` THEN
  SUBGOAL_THEN `&0 < (t * r + cB * cD)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PRODLT_TAC `(t * r + cB * cD)` `vD - ((&187 / &100) * r + (&19 / &25) * cD)` THEN
  PCT_PRODLT_TAC `&1 + (t * r + cB * cD)` `aB - &1` THEN
  ASM_CASES_TAC `t <= r` THENL
  [MP_TAC(SPECL [`cD:real`; `r:real`; `cB:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   PCT_PROD_TAC `t:real` `cB - cD:real` THEN PCT_PROD_TAC `cB:real` `r - t:real` THEN
   SUBGOAL_THEN `(t * cD - cB * r) <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`; `r:real`;
                 `t:real`; `cB:real`] C977NCO_UPPER_NEGATIVE_NONPOS) THEN
   ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
                   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
   PCT_PROD_TAC `--(t * cD - cB * r)` `&2 * cD - (&457 / &500) * r - uD` THEN
   SUBGOAL_THEN
    `(t * cD - cB * r) * (&2 * cD - (&457 / &500) * r) +
     (t * r + cB * cD) * ((&187 / &100) * r + (&19 / &25) * cD + &1) + &1 - &2 * cB - &3 * t =
     &1 + cB * (cD - &31 / &25 + (&77 / &500) * r pow 2 - (&13 / &100) * cD * r) +
     t * (r - &1 - (&13 / &100) * r pow 2 - (&77 / &500) * cD * r)` ASSUME_TAC THENL
   [UNDISCH_TAC `cD pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MP_TAC(SPECL [`cB:real`; `t:real`; `cD:real`; `r:real`] NBTC_FIRST_MARGIN) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN RASM_ARITH_TAC;
   SUBGOAL_THEN `r <= t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`cB:real`; `t:real`; `cD:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   PCT_PROD_TAC `t:real` `cD - cB:real` THEN PCT_PROD_TAC `cB:real` `t - r:real` THEN
   SUBGOAL_THEN `&0 <= (t * cD - cB * r)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`; `r:real`;
                 `t:real`; `cB:real`] C977NCO_UPPER_NEGATIVE_POS) THEN
   ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
                   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
   PCT_PROD_TAC `(t * cD - cB * r)` `uD + aB - ((&143 / &50) * cD - r)` THEN
   SUBGOAL_THEN
    `(t * cD - cB * r) * ((&143 / &50) * cD - r) +
     (t * r + cB * cD) * ((&187 / &100) * r + (&19 / &25) * cD + &1) + &1 - &2 * cB - &3 * t =
     &1 + cB * (cD - &31 / &25 + (&6 / &25) * r pow 2 - (&99 / &100) * cD * r) +
     t * (r - &7 / &50 - (&99 / &100) * r pow 2 - (&6 / &25) * cD * r)` ASSUME_TAC THENL
   [UNDISCH_TAC `cD pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MP_TAC(SPECL [`cB:real`; `t:real`; `cD:real`; `r:real`] NBTC_LAST_MARGIN) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN RASM_ARITH_TAC]);;
