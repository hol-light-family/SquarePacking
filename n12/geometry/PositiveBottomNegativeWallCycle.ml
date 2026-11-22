(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveBottomNegativeWallCycle.lean (Jatloe,    *)
(* N12-jatloe; namespace N12Compact.PositiveBottomNegativeWallCycle).        *)
(* One full three-square support cycle: positive singleton O, negative       *)
(* bottom wall D, negative central square B.  Lean upper/lower are           *)
(* ABT_upper/ABT_lower; a square with D.s = -r is cD sD uD vD aD with the    *)
(* hypothesis sD = --r.                                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/PositiveBottomNextAxes.ml";;

let PBNWC_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PBNWC_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PBNWC_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PBNWC_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PBNWC_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: defect (private) *)
let PBNWC_DEFECT = prove
 (`forall c s. c977cc_normal c s ==> s pow 2 / &2 <= &1 - c /\ &1 - c <= (&3 / &5) * s pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PBNWC_NORMAL_TAC THEN
  PBNWC_PROD_TAC `&1 - c` `(&3 / &5) * c - &2 / &5` THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - c`]);;

(* Lean: quadratic_between (private) *)
let PBNWC_QUADRATIC_BETWEEN = prove
 (`forall a b k low high x.
     &0 <= k /\ low <= x /\ x <= high /\
     &0 <= a + b * low - k * low pow 2 /\ &0 <= a + b * high - k * high pow 2
     ==> &0 <= a + b * x - k * x pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `low:real = high` THENL
  [SUBGOAL_THEN `x:real = low` SUBST1_TAC THENL [RASM_ARITH_TAC; ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < high - low` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PBNWC_PROD_TAC `high - x` `a + b * low - k * low pow 2` THEN
  PBNWC_PROD_TAC `x - low` `a + b * high - k * high pow 2` THEN
  PBNWC_PROD_TAC `k:real` `x - low` THEN
  PBNWC_PROD_TAC `high - x` `high - low` THEN
  PBNWC_PROD_TAC `k * (x - low)` `(high - x) * (high - low)` THEN
  SUBGOAL_THEN `&0 <= (high - low) * (a + b * x - k * x pow 2)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(high - low) * (a + b * x - k * x pow 2) =
     (high - x) * (a + b * low - k * low pow 2) + (x - low) * (a + b * high - k * high pow 2) +
     (k * (x - low)) * ((high - x) * (high - low))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
  NLIN_TAC ~deg2:true []);;

(* Lean: parallel_endpoint (private) *)
let PBNWC_PARALLEL_ENDPOINT = prove
 (`forall p q c t w. c977cc_normal p q /\ c977cc_normal c t /\ &0 <= w /\ w <= &10 / &7
     ==> &0 <= p * (&1 - &2 * c - &3 * t) + &2 * t + p * (&1 + c * t) - q * t pow 2 -
               p * w * ((&3 / &5) * t pow 2 - (&1 - c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PBNWC_USE PBNWC_DEFECT [`p:real`; `q:real`] THEN
  PBNWC_USE PBNWC_DEFECT [`c:real`; `t:real`] THEN PBNWC_NORMAL_TAC THEN
  PBNWC_PROD_TAC `p:real` `w:real` THEN
  PBNWC_PROD_TAC `p * w` `(&1 / &10) * t pow 2 - ((&3 / &5) * t pow 2 - (&1 - c))` THEN
  PBNWC_PROD_TAC `p:real` `t pow 2` THEN
  PBNWC_PROD_TAC `p * t pow 2` `&1 / &7 - w / &10` THEN
  SUBGOAL_THEN `p * w * ((&3 / &5) * t pow 2 - (&1 - c)) <= p * t pow 2 / &7`
  ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBNWC_PROD_TAC `p:real` `&2 - t` THEN
  PBNWC_PROD_TAC `p * (&2 - t)` `&1 - c - t pow 2 / &2` THEN
  PBNWC_PROD_TAC `t:real` `&2 * (&1 - p) - q pow 2` THEN
  PBNWC_PROD_TAC `p - &7 / &10` `t pow 2` THEN
  PBNWC_PROD_TAC `(p - &7 / &10) * t pow 2` `&6 / &7 - t / &2` THEN
  PBNWC_PROD_TAC `t:real` `(q - t / &2) pow 2` THEN
  PBNWC_PROD_TAC `t pow 2` `&1 - t` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: margin *)
let PBNWC_MARGIN = prove
 (`forall p q d r c t. c977cc_normal p q /\ c977cc_normal d r /\ c977cc_normal c t
     ==> &0 <= p * (&1 - &2 * c - &3 * t) + &2 * t + (p * c - q * t) * r +
               p * (t * r + c * d) + p * max (t * d - c * r) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PBNWC_USE PBNWC_DEFECT [`d:real`; `r:real`] THEN PBNWC_NORMAL_TAC THEN
  ASM_CASES_TAC `r <= t` THENL
  [PBNWC_USE C977CSB_COSINE_ORDER [`c:real`; `t:real`; `d:real`; `r:real`] THEN
   PBNWC_PROD_TAC `t:real` `d - c` THEN PBNWC_PROD_TAC `c:real` `t - r` THEN
   SUBGOAL_THEN `max (t * d - c * r) (&0) = t * d - c * r` SUBST1_TAC THENL
   [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   PBNWC_PROD_TAC `p:real` `c + t` THEN
   MP_TAC(SPECL [`p * (&1 - c - &2 * t) + &2 * t`; `t * (p - q)`;
                 `(&3 / &5) * p * (c + t)`; `&0`; `t:real`; `r:real`]
     PBNWC_QUADRATIC_BETWEEN) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [RASM_ARITH_TAC;
     RASM_ARITH_TAC; RASM_ARITH_TAC;
     PBNWC_PROD_TAC `p:real` `&1 - c` THEN PBNWC_PROD_TAC `t:real` `&1 - p` THEN
     NLIN_TAC ~deg2:false [];
     PBNWC_USE PBNWC_PARALLEL_ENDPOINT [`p:real`; `q:real`; `c:real`; `t:real`; `c + t`] THEN
     SUBGOAL_THEN
      `p * (&1 - c - &2 * t) + &2 * t + t * (p - q) * t - (&3 / &5) * p * (c + t) * t pow 2 =
       p * (&1 - &2 * c - &3 * t) + &2 * t + p * (&1 + c * t) - q * t pow 2 -
       p * (c + t) * ((&3 / &5) * t pow 2 - (&1 - c))` MP_TAC THENL
     [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     RASM_ARITH_TAC];
    DISCH_TAC] THEN
   PBNWC_PROD_TAC `p:real` `c + t` THEN
   PBNWC_PROD_TAC `p * (c + t)` `d - (&1 - (&3 / &5) * r pow 2)` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  PBNWC_USE C977CSB_COSINE_ORDER [`d:real`; `r:real`; `c:real`; `t:real`] THEN
  PBNWC_PROD_TAC `t:real` `c - d` THEN PBNWC_PROD_TAC `c:real` `r - t` THEN
  SUBGOAL_THEN `max (t * d - c * r) (&0) = &0` SUBST1_TAC THENL
  [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&5 / &7) * p - (&9 / &5) * q`;
                  SQ_NONNEG `(&9 / &5) * p + (&5 / &7) * q - &2`]
    [`(&9 / &5) * p + (&5 / &7) * q <= &2`] THEN
  PBNWC_PROD_TAC `p:real` `c:real` THEN
  MP_TAC(SPECL [`p * (&1 - c - &3 * t) + &2 * t`; `p * (t + c) - q * t`;
                `(&3 / &5) * p * c`; `t:real`; `&5 / &7`; `r:real`]
    PBNWC_QUADRATIC_BETWEEN) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [RASM_ARITH_TAC;
    RASM_ARITH_TAC; RASM_ARITH_TAC;
    PBNWC_USE PBNWC_PARALLEL_ENDPOINT [`p:real`; `q:real`; `c:real`; `t:real`; `c:real`] THEN
    SUBGOAL_THEN
     `p * (&1 - c - &3 * t) + &2 * t + (p * (t + c) - q * t) * t - (&3 / &5) * p * c * t pow 2 =
      p * (&1 - &2 * c - &3 * t) + &2 * t + p * (&1 + c * t) - q * t pow 2 -
      p * c * ((&3 / &5) * t pow 2 - (&1 - c))` MP_TAC THENL
    [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    PBNWC_PROD_TAC `t:real` `&2 - ((&9 / &5) * p + (&5 / &7) * q)` THEN
    PBNWC_PROD_TAC `p:real` `&1 - (&29 / &49) * c - (&17 / &35) * t` THEN
    NLIN_TAC ~deg2:false []];
   DISCH_TAC] THEN
  PBNWC_PROD_TAC `p:real` `c:real` THEN
  PBNWC_PROD_TAC `p * c` `d - (&1 - (&3 / &5) * r pow 2)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: singleton_upper *)
let PBNWC_SINGLETON_UPPER = prove
 (`forall cO sO uO vO aO.
     c977cc_normal cO sO /\ &1 < aO /\ &0 <= sO * uO + cO * vO /\ vO + aO <= cO - sO
     ==> &2 < uO + aO`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PBNWC_NORMAL_TAC THEN
  PBNWC_PROD_TAC `cO:real` `(cO - sO) - (vO + aO)` THEN
  PBNWC_PRODLT_TAC `aO - &1` `cO + sO` THEN
  PBNWC_PROD_TAC `&1 - cO` `cO - sO` THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PBNWC_POS_OF_MUL THEN
  EXISTS_TAC `sO:real` THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sO * ((uO + aO) - &2) =
    (sO * uO + cO * vO) + cO * (cO - sO - (vO + aO)) + (aO - &1) * (cO + sO) +
    (&1 - cO) * (cO - sO)` SUBST1_TAC THENL
  [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: own_transverse *)
let PBNWC_OWN_TRANSVERSE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD cB sB (uB:real) vB aB r t.
     sD = --r /\ sB = --t /\
     c977cc_normal cO sO /\ c977cc_normal cD r /\ c977cc_normal cB t /\
     aO = aD /\ aD = aB /\ &1 < aD /\
     &0 <= sO * uO + cO * vO /\ vO + aO <= cO - sO /\ lcont cD sD uD vD aD /\
     vB + aB <= &2 * cB + &3 * t /\
     uO + aO <= ABT_lower cD sD uD vD aD cO sO /\
     ABT_upper cD sD uD vD aD t cB <= vB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aD`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  PBNWC_USE PBNWC_SINGLETON_UPPER [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aB:real`] THEN
  PBNWC_USE PBNWC_MARGIN [`cO:real`; `sO:real`; `cD:real`; `r:real`; `cB:real`; `t:real`] THEN
  PBNWC_NORMAL_TAC THEN
  PBNWC_PROD_TAC `cD:real` `cO - sO` THEN PBNWC_PROD_TAC `sO:real` `cD - r` THEN
  SUBGOAL_THEN `&0 <= (cO * cD - sO * r)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBNWC_PROD_TAC `cO:real` `r:real` THEN PBNWC_PROD_TAC `sO:real` `cD:real` THEN
  PBNWC_PROD_TAC `t:real` `r:real` THEN PBNWC_PRODLT_TAC `cB:real` `cD:real` THEN
  PBNWC_PROD_TAC `cB:real` `cO - sO` THEN PBNWC_PROD_TAC `sO:real` `cB - t` THEN
  SUBGOAL_THEN `&0 <= (cO * cB - sO * t)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBNWC_USE C977NCO_LOWER_NEGATIVE_POS
    [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`; `r:real`; `cO:real`; `sO:real`] THEN
  SUBGOAL_THEN `ABT_upper cD (--r) uD vD aB t cB = ((t * cD - cB * r) * uD + (t * r + cB * cD) * vD + aB * ((t * r + cB * cD) + max (t * cD - cB * r) (&0)))` ASSUME_TAC THENL
  [ASM_CASES_TAC `&0 <= (t * cD - cB * r)` THENL
   [PBNWC_USE C977NCO_UPPER_NEGATIVE_POS
      [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`; `r:real`; `t:real`; `cB:real`] THEN
    SUBGOAL_THEN `max (t * cD - cB * r) (&0) = (t * cD - cB * r)` SUBST1_TAC THENL
    [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC];
    PBNWC_USE C977NCO_UPPER_NEGATIVE_NONPOS
      [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`; `r:real`; `t:real`; `cB:real`] THEN
    SUBGOAL_THEN `max (t * cD - cB * r) (&0) = &0` SUBST1_TAC THENL
    [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC]] THEN
   FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match [] `ABT_upper c s u v a nx ny = e`) o concl)) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= max (t * cD - cB * r) (&0)` ASSUME_TAC THENL
  [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cD * cD + --r * --r = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy; REAL_ABS_NEG]) THEN
  SUBGOAL_THEN `abs r = r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cD * vD - r * (uD + aB)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PBNWC_PROD_TAC `(cO * cB - sO * t)` `r:real` THEN PBNWC_PROD_TAC `cO:real` `max (t * cD - cB * r) (&0)` THEN
  PBNWC_PRODLT_TAC `cO:real` `(t * r + cB * cD)` THEN
  PBNWC_PRODLT_TAC `aB - &1` `((cO * cB - sO * t) * r + cO * ((t * r + cB * cD) + max (t * cD - cB * r) (&0))) + cO` THEN
  PBNWC_PROD_TAC `t:real` `((cO * cD - sO * r) * uD + (cO * r + sO * cD) * vD) - &2` THEN
  PBNWC_PROD_TAC `(cO * cB - sO * t)` `cD * vD - r * (uD + aB)` THEN
  PBNWC_PROD_TAC `cO:real` `(&2 * cB + &3 * t) - (vB + aB)` THEN
  PBNWC_PROD_TAC `cO:real` `vB - ((t * cD - cB * r) * uD + (t * r + cB * cD) * vD + aB * ((t * r + cB * cD) + max (t * cD - cB * r) (&0)))` THEN
  SUBGOAL_THEN
   `cO * (((t * cD - cB * r) * uD + (t * r + cB * cD) * vD + aB * ((t * r + cB * cD) + max (t * cD - cB * r) (&0))) - vB) =
    t * (((cO * cD - sO * r) * uD + (cO * r + sO * cD) * vD) - &2) + (cO * cB - sO * t) * (cD * vD - r * (uD + aB)) +
    cO * (&2 * cB + &3 * t - (vB + aB)) + (aB - &1) * (((cO * cB - sO * t) * r + cO * ((t * r + cB * cD) + max (t * cD - cB * r) (&0))) + cO) +
    (cO * (&1 - &2 * cB - &3 * t) + &2 * t + ((cO * cB - sO * t) * r + cO * ((t * r + cB * cD) + max (t * cD - cB * r) (&0))))` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;
