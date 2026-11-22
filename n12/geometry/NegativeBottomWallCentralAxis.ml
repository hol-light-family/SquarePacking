(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeBottomWallCentralAxis.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.NegativeBottomWallCentralAxis).          *)
(* The negative bottom singleton's upward separator cannot be followed by    *)
(* the central neighbour's transverse separator.  Lean upper/lower are       *)
(* ABT_upper/ABT_lower; positive_frame_wall_bounds is used through           *)
(* TSS_BOTTOM_WALL.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/PositiveBottomWallCentralAxis.ml";;

let NBWCA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let NBWCA_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let NBWCA_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let NBWCA_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let NBWCA_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let NBWCA_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let NBWCA_LOWER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_lower c s u v a nx ny = (nx * c + ny * s) * u + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC);;

(* Lean: arc (private) *)
let NBWCA_ARC = prove
 (`forall p q. c977cc_normal p q ==> &1 + (&4 / &5) * p * q <= p + q`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN NBWCA_NORMAL_TAC THEN
  NBWCA_PROD_TAC `p:real` `q:real` THEN
  NBWCA_PROD_TAC `p * q` `&6 / &5 - (&4 / &5) * (p + q)` THEN
  SUBGOAL_THEN `(p + q + &1) * (p + q - &1 - (&4 / &5) * p * q) =
                p * q * (&6 / &5 - (&4 / &5) * (p + q))` ASSUME_TAC THENL
  [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p + q - &1 - (&4 / &5) * p * q` MP_TAC THENL
  [MATCH_MP_TAC NBWCA_NONNEG_OF_MUL THEN EXISTS_TAC `p + q + &1` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: singleton_height *)
let NBWCA_SINGLETON_HEIGHT = prove
 (`forall cO (sO:real) uO vO aO q.
     c977cc_normal cO q /\ &1 < aO /\ cO - q <= uO /\ q * (uO + aO) <= cO * vO
     ==> cO + (&9 / &5) * q < vO + aO`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NBWCA_USE NBWCA_ARC [`cO:real`; `q:real`] THEN NBWCA_NORMAL_TAC THEN
  NBWCA_PROD_TAC `q:real` `uO - (cO - q)` THEN
  NBWCA_PRODLT_TAC `aO - &1` `cO + q` THEN
  SUBGOAL_THEN
   `cO * ((vO + aO) - (cO + (&9 / &5) * q)) =
    (cO * vO - q * (uO + aO)) + q * (uO - (cO - q)) + (aO - &1) * (cO + q) +
    (cO + q - &1 - (&4 / &5) * cO * q)` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + q pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC NBWCA_POS_OF_MUL THEN
  EXISTS_TAC `cO:real` THEN CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: support_width (private) *)
let NBWCA_SUPPORT_WIDTH = prove
 (`forall d r c t. c977cc_normal d r /\ c977cc_normal c t
     ==> c + (&2 / &5) * t <= (t * d + c * r) + (c * d - t * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NBWCA_NORMAL_TAC THEN
  NBWCA_PROD_TAC `c - t` `d + r - &1` THEN
  NBWCA_PROD_TAC `t:real` `&2 * d - &7 / &5` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: horizontal_margin (private) *)
let NBWCA_HORIZONTAL_MARGIN = prove
 (`forall d r c t. c977cc_normal d r /\ c977cc_normal c t
     ==> &0 <= d + c * d * (d + r - &1) + t * (d * (d - r - &2 / &5) - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NBWCA_NORMAL_TAC THEN
  NBWCA_PROD_TAC `d:real` `d + r - &1` THEN
  NBWCA_PROD_TAC `c - t` `d * (d + r - &1)` THEN
  NBWCA_PROD_TAC `d:real` `&1 - d` THEN
  SUBGOAL_THEN `&2 * d pow 2 - (&7 / &5) * d - &1 <= &0` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NBWCA_PROD_TAC `&5 / &7 - t` `--(&2 * d pow 2 - (&7 / &5) * d - &1)` THEN
  NBWCA_PROD_TAC `d - r` `d + r` THEN
  NLIN_FACTS_TAC [] [`&0 <= &2 * d pow 2 - &1`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: own_transverse *)
let NBWCA_OWN_TRANSVERSE = prove
 (`forall cO (sO:real) uO vO aO cD sD uD vD aD cB (sB:real) (uB:real) vB aB q t.
     c977cc_normal cO q /\ c977cc_normal cD sD /\ c977cc_normal cB t /\
     aO = aD /\ aD = aB /\ &1 < aD /\ &0 < q /\
     cO - q <= uO /\ q * (uO + aO) <= cO * vO /\
     lcont cD sD uD vD aD /\ linside cD sD uD vD aD (&13 / &5) (&1) /\
     vB + aB <= &2 * cB + &3 * t /\
     vO + aO <= ABT_lower cD sD uD vD aD q cO /\
     ABT_upper cD sD uD vD aD t cB <= vB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aD`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aD:real = aB`)) THEN
  NBWCA_USE NBWCA_SINGLETON_HEIGHT
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aD:real`; `q:real`] THEN
  NBWCA_USE NBWCA_SUPPORT_WIDTH [`cD:real`; `sD:real`; `cB:real`; `t:real`] THEN
  NBWCA_USE NBWCA_HORIZONTAL_MARGIN [`cD:real`; `sD:real`; `cB:real`; `t:real`] THEN
  NBWCA_NORMAL_TAC THEN
  SUBGOAL_THEN `cD * cD + sD * sD = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  SUBGOAL_THEN `abs sD = sD` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sD * uD + cD * vD` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NBWCA_PROD_TAC `q:real` `cD:real` THEN NBWCA_PROD_TAC `cO:real` `sD:real` THEN
  NBWCA_PROD_TAC `cD:real` `cO - q` THEN NBWCA_PROD_TAC `q:real` `cD - sD` THEN
  NBWCA_PROD_TAC `t:real` `cD:real` THEN NBWCA_PROD_TAC `cB:real` `sD:real` THEN
  NBWCA_PROD_TAC `cD:real` `cB - t` THEN NBWCA_PROD_TAC `t:real` `cD - sD` THEN
  SUBGOAL_THEN `&0 <= (cO * cD - q * sD) /\ &0 <= (cB * cD - t * sD)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NBWCA_USE C696PC_UPPER_PP
    [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `t:real`; `cB:real`] THEN
  NBWCA_USE NBWCA_LOWER_PP
    [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `q:real`; `cO:real`] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if can (term_match [] `ABT_upper c s u v a nx ny = e`) (concl th) ||
                                    can (term_match [] `ABT_lower c s u v a nx ny = e`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "")) THEN
  SUBGOAL_THEN `cO + (&9 / &5) * q <= ((q * cD + cO * sD) * uD + (cO * cD - q * sD) * vD)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (q * cB - cO * t)` THENL
  [NBWCA_PROD_TAC `t:real` `((q * cD + cO * sD) * uD + (cO * cD - q * sD) * vD) - (cO + (&9 / &5) * q)` THEN
   NBWCA_PROD_TAC `(q * cB - cO * t)` `sD * uD + cD * vD` THEN
   NBWCA_PRODLT_TAC `q:real` `&1 + (t * cD + cB * sD) + (cB * cD - t * sD)` THEN
   NBWCA_PRODLT_TAC `aD - &1` `q * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD))` THEN
   NBWCA_PROD_TAC `q:real` `((t * cD + cB * sD) + (cB * cD - t * sD)) - (cB + (&2 / &5) * t)` THEN
   NBWCA_PROD_TAC `q:real` `&1 - cB` THEN
   NBWCA_PROD_TAC `t:real` `cO - (&4 / &5) * q` THEN
   SUBGOAL_THEN `&0 <= t * (cO + (&9 / &5) * q) + q * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD) - &2 * cB - &3 * t)`
   ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   NBWCA_PROD_TAC `q:real` `(&2 * cB + &3 * t) - (((t * cD + cB * sD) * (uD + aD) + (cB * cD - t * sD) * (vD + aD)) + aD)` THEN
   SUBGOAL_THEN
    `q * (((t * cD + cB * sD) * (uD + aD) + (cB * cD - t * sD) * (vD + aD)) + aD - (&2 * cB + &3 * t)) =
     t * (((q * cD + cO * sD) * uD + (cO * cD - q * sD) * vD) - (cO + (&9 / &5) * q)) + (q * cB - cO * t) * (sD * uD + cD * vD) +
     (aD - &1) * (q * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD))) +
     (t * (cO + (&9 / &5) * q) + q * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD) - &2 * cB - &3 * t))` ASSUME_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   NBWCA_PROD_TAC `q:real` `cB:real` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q < cO` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `cO:real = q` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   NBWCA_PROD_TAC `q:real` `cB - t` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NBWCA_PRODLT_TAC `cD:real` `cO - q` THEN
  NBWCA_PROD_TAC `q:real` `cD - sD` THEN
  SUBGOAL_THEN `&0 < (cO * cD - q * sD)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((cB * cD - t * sD) * (&1 - cB - (&6 / &5) * t + (t * cD + cB * sD) + (cB * cD - t * sD)))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NBWCA_PROD_TAC `--((q * cB - cO * t))` `(cD + cB * cD * (cD + sD - &1) + t * (cD * (cD - sD - &2 / &5) - &1))` THEN
  NBWCA_PROD_TAC `q:real` `((cB * cD - t * sD) * (&1 - cB - (&6 / &5) * t + (t * cD + cB * sD) + (cB * cD - t * sD)))` THEN
  SUBGOAL_THEN `t * ((cB * cD - t * sD) * (cO + (&9 / &5) * q) - (q * cB - cO * t) * ((&13 / &5) * cD + sD - &1) + (cO * cD - q * sD) * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD) - &2 * cB - &3 * t)) = --((q * cB - cO * t)) * (cD + cB * cD * (cD + sD - &1) + t * (cD * (cD - sD - &2 / &5) - &1)) + q * ((cB * cD - t * sD) * (&1 - cB - (&6 / &5) * t + (t * cD + cB * sD) + (cB * cD - t * sD)))` ASSUME_TAC THENL
  [CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((cB * cD - t * sD) * (cO + (&9 / &5) * q) - (q * cB - cO * t) * ((&13 / &5) * cD + sD - &1) + (cO * cD - q * sD) * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD) - &2 * cB - &3 * t))` ASSUME_TAC THENL
  [MATCH_MP_TAC NBWCA_NONNEG_OF_MUL THEN EXISTS_TAC `t:real` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NBWCA_PRODLT_TAC `(cO * cD - q * sD)` `&1 + (cB * cD - t * sD)` THEN
  NBWCA_PROD_TAC `(cB * cD - t * sD)` `(q * cD + cO * sD)` THEN
  SUBGOAL_THEN `((cO * cD - q * sD) * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD)) + (q * cB - cO * t)) = (cO * cD - q * sD) * (&1 + (cB * cD - t * sD)) + (cB * cD - t * sD) * (q * cD + cO * sD)` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((cO * cD - q * sD) * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD)) + (q * cB - cO * t))` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NBWCA_PROD_TAC `(cB * cD - t * sD)` `((q * cD + cO * sD) * uD + (cO * cD - q * sD) * vD) - (cO + (&9 / &5) * q)` THEN
  MP_TAC(ASSUME `linside cD sD uD vD aD (&13 / &5) (&1)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NBWCA_PROD_TAC `--((q * cB - cO * t))` `(uD + aD) - ((&13 / &5) * cD + sD)` THEN
  NBWCA_PRODLT_TAC `aD - &1` `((cO * cD - q * sD) * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD)) + (q * cB - cO * t))` THEN
  NBWCA_PROD_TAC `(cO * cD - q * sD)` `(&2 * cB + &3 * t) - (((t * cD + cB * sD) * (uD + aD) + (cB * cD - t * sD) * (vD + aD)) + aD)` THEN
  SUBGOAL_THEN
   `(cO * cD - q * sD) * (((t * cD + cB * sD) * (uD + aD) + (cB * cD - t * sD) * (vD + aD)) + aD - (&2 * cB + &3 * t)) =
    (cB * cD - t * sD) * (((q * cD + cO * sD) * uD + (cO * cD - q * sD) * vD) - (cO + (&9 / &5) * q)) +
    --((q * cB - cO * t)) * ((uD + aD) - ((&13 / &5) * cD + sD)) + (aD - &1) * ((cO * cD - q * sD) * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD)) + (q * cB - cO * t)) + ((cB * cD - t * sD) * (cO + (&9 / &5) * q) - (q * cB - cO * t) * ((&13 / &5) * cD + sD - &1) + (cO * cD - q * sD) * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD) - &2 * cB - &3 * t))` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;
