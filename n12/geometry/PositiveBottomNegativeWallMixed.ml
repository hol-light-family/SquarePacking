(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveBottomNegativeWallMixed.lean (Jatloe,    *)
(* N12-jatloe; namespace N12Compact.PositiveBottomNegativeWallMixed).        *)
(* The remaining mixed negative-wall selector.  Lean upper/lower are         *)
(* ABT_upper/ABT_lower; a square with D.s = -r is cD sD uD vD aD with the    *)
(* hypothesis sD = --r.                                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/PositiveBottomNegativeWallCycle.ml";;
needs "n12/geometry/PositiveBottomSupport.ml";;

let PBNWM_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PBNWM_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

let PBNWM_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: wide (private) *)
let PBNWM_WIDE = prove
 (`forall c t. c977cc_normal c t /\ t <= &3 / &10 ==> &9 / &10 <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PBNWM_NORMAL_TAC THEN
  PBNWM_PROD_TAC `&3 / &10 - t` `&3 / &10 + t` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  PBNWM_PROD_TAC `&9 / &10 - c` `&9 / &10 + c` THEN NLIN_TAC ~deg2:false []);;

(* Lean: virtual_bounds (private) *)
let PBNWM_VIRTUAL_BOUNDS = prove
 (`forall d r X Y. c977cc_normal d r /\ &457 / &500 <= Y /\ Y <= &13 / &10 /\
     (X <= &21 / &10 \/ (X <= &47 / &20 /\ r <= &3 / &10))
     ==> (&2 + r pow 2 * (X - &2) + d * r * (Y - &457 / &500) - r) <= &2 /\ (&2 + r pow 2 * (X - &2) + d * r * (Y - &457 / &500) - r) + (Y - d + d * r * (X - &2) + r pow 2 * (&457 / &500 - Y)) <= &5 / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  PBNWM_NORMAL_TAC THEN
  PBNWM_PROD_TAC `r pow 2` `Y - &457 / &500` THEN
  PBNWM_PROD_TAC `d:real` `&13 / &10 - Y` THEN
  PBNWM_PROD_TAC `r:real` `&1 - d` THEN
  PBNWM_PROD_TAC `d:real` `r:real` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [PBNWM_PROD_TAC `r:real` `&21 / &10 - X` THEN
   SUBGOAL_THEN `r * (X - &2) + d * (Y - &457 / &500) <= &1 / &2` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PBNWM_PROD_TAC `r:real` `&1 / &2 - (r * (X - &2) + d * (Y - &457 / &500))` THEN
   PBNWM_PROD_TAC `d * r` `&21 / &10 - X` THEN
   SUBGOAL_THEN `(&2 + r pow 2 * (X - &2) + d * r * (Y - &457 / &500) - r) <= &2 - r / &2 /\ (Y - d + d * r * (X - &2) + r pow 2 * (&457 / &500 - Y)) <= &13 / &10 - d + r / &10` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   CONJ_TAC THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  PBNWM_USE PBNWM_WIDE [`d:real`; `r:real`] THEN
  PBNWM_PROD_TAC `r:real` `&47 / &20 - X` THEN
  SUBGOAL_THEN `r * (X - &2) + d * (Y - &457 / &500) <= &1 / &2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBNWM_PROD_TAC `r:real` `&1 / &2 - (r * (X - &2) + d * (Y - &457 / &500))` THEN
  PBNWM_PROD_TAC `d * r` `&47 / &20 - X` THEN
  SUBGOAL_THEN `(&2 + r pow 2 * (X - &2) + d * r * (Y - &457 / &500) - r) <= &2 - r / &2 /\ (Y - d + d * r * (X - &2) + r pow 2 * (&457 / &500 - Y)) <= &13 / &10 - d + (&7 / &20) * r`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: through_wall (private) *)
let PBNWM_THROUGH_WALL = prove
 (`forall cD sD uD vD aD cB sB uB vB aB r p q X Y.
     sD = --r /\ c977cc_normal p q /\ c977cc_normal cD r /\ aD = aB /\ &1 <= aD /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     vD + aD <= ABT_lower cB sB uB vB aB r cD /\
     ABT_lower cB sB uB vB aB r cD <= r * X + cD * Y /\
     &457 / &500 <= Y /\ Y <= &13 / &10 /\
     (X <= &21 / &10 \/ (X <= &47 / &20 /\ r <= &3 / &10))
     ==> ABT_lower cD sD uD vD aD p q <= &2 * p + q / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  PBNWM_USE PBNWM_VIRTUAL_BOUNDS [`cD:real`; `r:real`; `X:real`; `Y:real`] THEN
  PBNWM_NORMAL_TAC THEN
  PBNWM_PROD_TAC `cD:real` `p - q` THEN PBNWM_PROD_TAC `q:real` `cD - r` THEN
  SUBGOAL_THEN `&0 <= p * cD - q * r` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBNWM_PROD_TAC `p:real` `r:real` THEN PBNWM_PROD_TAC `q:real` `cD:real` THEN
  MP_TAC(ASSUME `linside cD (--r) uD vD aD (&2) (&457 / &500)`) THEN
  REWRITE_TAC[C977NCO_NEG_BANDS] THEN STRIP_TAC THEN
  PBNWM_PROD_TAC `p * cD - q * r` `(cD * &2 - r * &457 / &500) - uD` THEN
  PBNWM_PROD_TAC `p * r + q * cD` `(r * X + cD * Y - &1) - vD` THEN
  PBNWM_USE C977NCO_LOWER_NEGATIVE_POS
    [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`; `r:real`; `p:real`; `q:real`] THEN
  SUBGOAL_THEN
   `(p * cD - q * r) * (&2 * cD - (&457 / &500) * r) + (p * r + q * cD) * (r * X + cD * Y - &1) =
    p * (&2 + r pow 2 * (X - &2) + cD * r * (Y - &457 / &500) - r) + q * (Y - cD + cD * r * (X - &2) + r pow 2 * (&457 / &500 - Y))` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PBNWM_PROD_TAC `p - q` `&2 - (&2 + r pow 2 * (X - &2) + cD * r * (Y - &457 / &500) - r)` THEN
  PBNWM_PROD_TAC `q:real` `&5 / &2 - ((&2 + r pow 2 * (X - &2) + cD * r * (Y - &457 / &500) - r) + (Y - cD + cD * r * (X - &2) + r pow 2 * (&457 / &500 - Y)))` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: support_bound *)
let PBNWM_SUPPORT_BOUND = prove
 (`forall cD sD uD vD aD cB sB uB vB aB r t p q.
     sD = --r /\ sB = --t /\
     c977cc_normal p q /\ c977cc_normal cD r /\ c977cc_normal cB t /\
     aD = aB /\ &1 <= aD /\ t <= &3 / &10 /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     vD + aD <= ABT_lower cB sB uB vB aB r cD
     ==> ABT_lower cD sD uD vD aD p q <= &2 * p + q / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  PBNWM_USE PBNWM_WIDE [`cB:real`; `t:real`] THEN PBNWM_NORMAL_TAC THEN
  PBNWM_PROD_TAC `r:real` `t:real` THEN PBNWM_PROD_TAC `cD:real` `cB:real` THEN
  PBNWM_PROD_TAC `cB:real` `t:real` THEN
  ASM_CASES_TAC `t <= r` THENL
  [PBNWM_USE C977CSB_COSINE_ORDER [`cD:real`; `r:real`; `cB:real`; `t:real`] THEN
   PBNWM_PROD_TAC `t:real` `cB - cD` THEN PBNWM_PROD_TAC `cB:real` `r - t` THEN
   SUBGOAL_THEN `&0 <= (r * cB - cD * t)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PBNWM_USE C977NCO_LOWER_NEGATIVE_POS
     [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`; `r:real`; `cD:real`] THEN
   PBNWM_PROD_TAC `(r * cB - cD * t)` `(&3 * cB - t) - (uB + aB)` THEN
   PBNWM_PROD_TAC `(r * t + cD * cB)` `(&2 * cB + &3 * t) - (vB + aB)` THEN
   PBNWM_PROD_TAC `(r * cB - cD * t) + (r * t + cD * cB)` `aB - &1` THEN
   SUBGOAL_THEN `(r * cB - cD * t) * (&3 * cB - t - &1) + (r * t + cD * cB) * (&2 * cB + &3 * t - &1) = r * (&3 + cB * t - cB - t) + cD * (&2 - t pow 2 + t - cB)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB r cD <= r * (&3 + cB * t - cB - t) + cD * (&2 - t pow 2 + t - cB)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PBNWM_PROD_TAC `t:real` `&1 - cB` THEN PBNWM_PROD_TAC `cB:real` `&1 - cB` THEN
   MATCH_MP_TAC PBNWM_THROUGH_WALL THEN
   MAP_EVERY EXISTS_TAC [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`;
                         `r:real`; `(&3 + cB * t - cB - t)`; `(&2 - t pow 2 + t - cB)`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
   TRY(DISJ1_TAC) THEN NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - cB`];
   ALL_TAC] THEN
  PBNWM_USE C977CSB_COSINE_ORDER [`cB:real`; `t:real`; `cD:real`; `r:real`] THEN
  PBNWM_PROD_TAC `t:real` `cD - cB` THEN PBNWM_PROD_TAC `cB:real` `t - r` THEN
  SUBGOAL_THEN `(r * cB - cD * t) <= &0` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBNWM_USE C977NCO_LOWER_NEGATIVE_NONPOS
    [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`; `r:real`; `cD:real`] THEN
  MP_TAC(ASSUME `linside cB (--t) uB vB aB (&47 / &20) (&33 / &20)`) THEN
  REWRITE_TAC[C977NCO_NEG_BANDS] THEN STRIP_TAC THEN
  PBNWM_PROD_TAC `--((r * cB - cD * t))` `(uB + aB) - ((&47 / &20) * cB - (&33 / &20) * t)` THEN
  PBNWM_PROD_TAC `(r * t + cD * cB)` `(&2 * cB + &3 * t) - (vB + aB)` THEN
  PBNWM_PROD_TAC `(r * t + cD * cB)` `aB - &1` THEN
  SUBGOAL_THEN
   `(r * cB - cD * t) * ((&47 / &20) * cB - (&33 / &20) * t) + (r * t + cD * cB) * (&2 * cB + &3 * t - &1) =
    r * (&47 / &20 + (&13 / &20) * t pow 2 + (&7 / &20) * cB * t - t) + cD * (&2 - (&7 / &20) * t pow 2 + (&13 / &20) * cB * t - cB)` ASSUME_TAC THENL
  [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB r cD <= r * (&47 / &20 + (&13 / &20) * t pow 2 + (&7 / &20) * cB * t - t) + cD * (&2 - (&7 / &20) * t pow 2 + (&13 / &20) * cB * t - cB)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBNWM_PROD_TAC `t:real` `&1 - cB` THEN
  PBNWM_PROD_TAC `&3 / &10 - t` `&3 / &10 + t` THEN
  PBNWM_PROD_TAC `t:real` `&1 - (&13 / &20) * t - (&7 / &20) * cB` THEN
  MATCH_MP_TAC PBNWM_THROUGH_WALL THEN
  MAP_EVERY EXISTS_TAC [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`;
                        `r:real`; `(&47 / &20 + (&13 / &20) * t pow 2 + (&7 / &20) * cB * t - t)`; `(&2 - (&7 / &20) * t pow 2 + (&13 / &20) * cB * t - cB)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(DISJ2_TAC) THEN TRY CONJ_TAC THEN NLIN_TAC ~deg2:false [SQ_NONNEG `t:real`]);;

(* Lean: own_wall_transverse *)
let PBNWM_OWN_WALL_TRANSVERSE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD cB sB uB vB aB r t.
     sD = --r /\ sB = --t /\
     c977cc_normal cO sO /\ c977cc_normal cD r /\ c977cc_normal cB t /\
     aO = aD /\ aD = aB /\ &1 < aD /\ t <= &3 / &10 /\
     &0 <= sO * uO + cO * vO /\ vO + aO <= cO - sO /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     uO + aO <= ABT_lower cD sD uD vD aD cO sO /\
     vD + aD <= ABT_lower cB sB uB vB aB r cD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PBNWM_USE PBS_OWN_AXIS [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] THEN
  PBNWM_USE PBNWM_SUPPORT_BOUND
    [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`; `t:real`;
     `cO:real`; `sO:real`] THEN
  RASM_ARITH_TAC);;
