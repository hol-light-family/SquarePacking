(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativePositiveBottom.lean (Jatloe).      *)
(* An incoming positive central axis cannot coexist with a positive bottom   *)
(* wall D below the negative southeast neighbour B on the wall's axis.       *)
(* Normal: c977cc_normal; lower: ABT_lower; B.s = -t written sB = --t;       *)
(* lower_negative_pos/nonpos: C977NCO_LOWER_NEGATIVE_POS/NONPOS;             *)
(* positive_frame_wall_bounds: C977WC_POSITIVE_FRAME_WALL_BOUNDS.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralNegativeBottomAxes.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;
needs "n12/geometry/C977WallChains.ml";;

(* Lean: coefficients (private) *)
let CNPB_COEFFICIENTS = prove
 (`forall c t d r. c977cc_normal c t /\ c977cc_normal d r
     ==> d pow 2 * (c + t - &1 - c * t) +
         c * (&1 - d - (&43 / &500) * r pow 2 - d * r * c) <= &0 /\
         d * r * (t - &1 + c * t) + d pow 2 * (t pow 2 - &2 * t) + d * t -
         (&457 / &500) * t * r pow 2 <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `d:real` REAL_LE_POW_2) THEN
  REPEAT DISCH_TAC THEN
  PCT_PROD_TAC `d - r:real` `d + r:real` THEN
  SUBGOAL_THEN `r pow 2 <= &1 / &2` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * t <= &1 / &2 /\ d * r <= &1 / &2` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL [NLIN_TAC [SQ_NONNEG `c - t:real`]; NLIN_TAC [SQ_NONNEG `d - r:real`]];
   ALL_TAC] THEN
  PCT_PROD_TAC `r:real` `&21 * d - &20 * r` THEN
  SUBGOAL_THEN `&1 - d <= (&3 / &7) * r` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCT_PRODLT_TAC `&7 - &7 * d - &3 * r` `&7 + &7 * d + &3 * r` THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  PCT_PROD_TAC `d - &7 / &10` `c:real` THEN
  SUBGOAL_THEN `&49 / &100 <= d * c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `r:real` `d * c - &49 / &100` THEN
  SUBGOAL_THEN `&1 - d - (&43 / &500) * r pow 2 - d * r * c <= &0` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `&1 - c` `&1 - t` THEN
  PCT_PROD_TAC `d pow 2` `(&1 - c) * (&1 - t)` THEN
  PCT_PROD_TAC `c:real` `--(&1 - d - (&43 / &500) * r pow 2 - d * r * c)` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&1 - d` REAL_LE_POW_2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `d <= &1 - r pow 2 / &2` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `t:real` `(&1 - r pow 2 / &2) - d` THEN
  SUBGOAL_THEN
   `d * r * (t - &1 + c * t) + d pow 2 * (t pow 2 - &2 * t) + d * t -
    (&457 / &500) * t * r pow 2 =
    t * (t - &1) + d * r * (t - &1 + c * t) + t * r pow 2 * (&293 / &500 - t) +
    t * (d - &1 + r pow 2 / &2)` ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCT_PROD_TAC `d:real` `r:real` THEN PCT_PROD_TAC `t:real` `r pow 2` THEN
  ASM_CASES_TAC `t <= &1 / &2` THENL
  [PCT_PROD_TAC `t:real` `&1 - c` THEN
   SUBGOAL_THEN `t - &1 + c * t <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   PCT_PROD_TAC `d * r` `--(t - &1 + c * t)` THEN
   SUBGOAL_THEN `r pow 2 * (&293 / &500 - t) <= &293 / &1000` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   PCT_PROD_TAC `t:real` `&293 / &1000 - r pow 2 * (&293 / &500 - t)` THEN
   PCT_PROD_TAC `t:real` `&1 / &2 - t` THEN
   RASM_ARITH_TAC;
   PCT_PROD_TAC `d * r` `&1 / &2 - c * t` THEN
   PCT_PROD_TAC `&1 / &2 - d * r` `t - &1 / &2` THEN
   SUBGOAL_THEN `d * r * (t - &1 + c * t) <= t / &2 - &1 / &4` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   PCT_PROD_TAC `r pow 2` `t - &1 / &2` THEN
   SUBGOAL_THEN `r pow 2 * (&293 / &500 - t) <= &43 / &1000` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   PCT_PROD_TAC `t:real` `&43 / &1000 - r pow 2 * (&293 / &500 - t)` THEN
   SUBGOAL_THEN `t <= &5 / &7` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   PCT_PROD_TAC `t:real` `&5 / &7 - t` THEN
   RASM_ARITH_TAC]);;

(* Lean: impossible *)
let CNPB_IMPOSSIBLE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB t C S.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal C S /\ c977cc_normal cB t /\ c977cc_normal cD sD /\
     sB = --t /\ &1 < aB /\ &1 <= aD /\ lcont cD sD uD vD aD /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     vB + aB <= &2 * cB + &3 * t /\
     &2 * (C + S) < ABT_lower cB sB uB vB aB C S /\
     vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  MP_TAC(SPECL [`cB:real`; `t:real`; `cD:real`; `sD:real`] CNPB_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < C /\ &0 < cB /\ &0 < cD` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN UNDISCH_TAC `lcont cD sD uD vD aD` THEN REWRITE_TAC[lcont] THEN
   DISCH_THEN(MP_TAC o SPECL [`x:real`; `y:real`]) THEN ASM_SIMP_TAC[];
   REWRITE_TAC[lcy] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= sD * uD + cD * vD` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `linside cD sD uD vD aD (&2) (&457 / &500)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  PCT_PROD_TAC `sD:real` `&2 * cD + (&457 / &500) * sD - uD` THEN
  PCT_PROD_TAC `cD:real` `aD - &1` THEN
  SUBGOAL_THEN `cD - &2 * cD * sD - (&457 / &500) * sD pow 2 <= cD * (vD + aD)`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `cB:real` `C - S:real` THEN PCT_PROD_TAC `S:real` `cB - t:real` THEN
  PCT_PROD_TAC `C:real` `t:real` THEN PCT_PROD_TAC `S:real` `cB:real` THEN
  PCT_PROD_TAC `sD:real` `cB:real` THEN PCT_PROD_TAC `cD:real` `t:real` THEN
  PCT_PROD_TAC `cB:real` `cD - sD:real` THEN PCT_PROD_TAC `sD:real` `cB - t:real` THEN
  PCT_PRODLT_TAC `C:real` `cD:real` THEN PCT_PROD_TAC `S:real` `sD:real` THEN
  SUBGOAL_THEN `&0 <= (C * cB - S * t) /\ &0 <= (C * t + S * cB) /\ (--sD * cB - cD * t) <= &0 /\ &0 <= (cD * cB - sD * t) /\ &0 < (C * cD + S * sD)`
  STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                `C:real`; `S:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                `--sD`; `cD:real`] C977NCO_LOWER_NEGATIVE_NONPOS) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  PCT_PROD_TAC `--(--sD * cB - cD * t)` `((C * cB - S * t) * uB + (C * t + S * cB) * vB) - &2 * (C + S)` THEN
  PCT_PROD_TAC `(C * cB - S * t)` `((--sD * cB - cD * t) * (uB + aB) + (cD * cB - sD * t) * vB) - (vD + aD)` THEN
  PCT_PROD_TAC `(C * cD + S * sD)` `(&2 * cB + &3 * t) - (vB + aB)` THEN
  PCT_PROD_TAC `--(--sD * cB - cD * t)` `(C * cB - S * t)` THEN
  PCT_PRODLT_TAC `aB - &1` `(C * cD + S * sD) - (--sD * cB - cD * t) * (C * cB - S * t)` THEN
  SUBGOAL_THEN `--(--sD * cB - cD * t) * ((C * cB - S * t) * uB + (C * t + S * cB) * vB) + (C * cB - S * t) * ((--sD * cB - cD * t) * (uB + aB) + (cD * cB - sD * t) * vB) =
                (C * cD + S * sD) * vB + (--sD * cB - cD * t) * (C * cB - S * t) * aB` ASSUME_TAC THENL
  [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (C * cD + S * sD) * (&2 * cB + &3 * t - &1) + (--sD * cB - cD * t) * (C * cB - S * t) + &2 * (--sD * cB - cD * t) * (C + S) -
                    (C * cB - S * t) * (vD + aD)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PRODLT_TAC `cD:real` `(C * cD + S * sD) * (&2 * cB + &3 * t - &1) + (--sD * cB - cD * t) * (C * cB - S * t) +
                            &2 * (--sD * cB - cD * t) * (C + S) - (C * cB - S * t) * (vD + aD)` THEN
  PCT_PROD_TAC `(C * cB - S * t)` `cD * (vD + aD) - (cD - &2 * cD * sD - (&457 / &500) * sD pow 2)` THEN
  PCT_PROD_TAC `C:real`
    `--(cD pow 2 * (cB + t - &1 - cB * t) +
        cB * (&1 - cD - (&43 / &500) * sD pow 2 - cD * sD * cB))` THEN
  PCT_PROD_TAC `S:real`
    `--(cD * sD * (t - &1 + cB * t) + cD pow 2 * (t pow 2 - &2 * t) + cD * t -
        (&457 / &500) * t * sD pow 2)` THEN
  SUBGOAL_THEN
   `cD * ((C * cD + S * sD) * (&2 * cB + &3 * t - &1) + (--sD * cB - cD * t) * (C * cB - S * t) + &2 * (--sD * cB - cD * t) * (C + S)) -
    (C * cB - S * t) * (cD - &2 * cD * sD - (&457 / &500) * sD pow 2) =
    C * (cD pow 2 * (cB + t - &1 - cB * t) +
         cB * (&1 - cD - (&43 / &500) * sD pow 2 - cD * sD * cB)) +
    S * (cD * sD * (t - &1 + cB * t) + cD pow 2 * (t pow 2 - &2 * t) + cD * t -
         (&457 / &500) * t * sD pow 2)` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;
