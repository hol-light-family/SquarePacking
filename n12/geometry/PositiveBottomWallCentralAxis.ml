(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveBottomWallCentralAxis.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.PositiveBottomWallCentralAxis).          *)
(* Both longitudinal ways in which the positive bottom singleton precedes a  *)
(* positive bottom wall contradict the central transverse separator.         *)
(* Lean upper/lower are ABT_upper/ABT_lower; positive_frame_wall_bounds is   *)
(* used through TSS_BOTTOM_WALL.                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/PositiveBottomSupport.ml";;

let PBWCA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PBWCA_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PBWCA_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PBWCA_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* lower support with a nonnegative first coefficient (helper) *)
let PBWCA_LOWER_PM = prove
 (`forall c s u v a nx ny. &0 < a /\ &0 <= nx * c + ny * s
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * u + (--nx * s + ny * c) * v + a * min (--nx * s + ny * c) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REWRITE_TAC[real_min] THEN COND_CASES_TAC THENL
  [ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`];
   ASM_SIMP_TAC[REAL_ARITH `~(x <= &0) ==> abs x = x`]] THEN
  REAL_ARITH_TAC);;

(* Lean: disk (private) *)
let PBWCA_DISK = prove
 (`forall d r c t. c977cc_normal d r /\ c977cc_normal c t
     ==> &0 <= &1 - c * (&2 - d - r) - t * (&1 - d + r / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PBWCA_NORMAL_TAC THEN
  PBWCA_PROD_TAC `&1 - d` `(&59 / &100) * d - &41 / &100` THEN
  NLIN_FACTS_TAC [] [`&1 - d <= (&59 / &100) * r pow 2`] THEN
  PBWCA_PROD_TAC `r:real` `&5 / &7 - r` THEN
  PBWCA_PROD_TAC `r:real` `&1 - d` THEN
  NLIN_FACTS_TAC [] [`(&2 - d - r) pow 2 + (&1 - d + r / &2) pow 2 <= &1`] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `(&2 - d - r) - c`; SQ_NONNEG `(&1 - d + r / &2) - t`]);;

(* Lean: of_entry *)
let PBWCA_OF_ENTRY = prove
 (`forall cD sD uD vD aD cB (sB:real) (uB:real) vB aB t.
     c977cc_normal cD sD /\ c977cc_normal cB t /\ aD = aB /\ &1 < aD /\
     lcont cD sD uD vD aD /\ vB + aB <= &2 * cB + &3 * t /\
     &2 * cD + sD / &2 <= uD /\ ABT_upper cD sD uD vD aD t cB <= vB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aD:real = aB`)) THEN
  PBWCA_USE PBWCA_DISK [`cD:real`; `sD:real`; `cB:real`; `t:real`] THEN
  PBWCA_NORMAL_TAC THEN
  SUBGOAL_THEN `cD * cD + sD * sD = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  SUBGOAL_THEN `abs sD = sD` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sD * uD + cD * vD` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PBWCA_PROD_TAC `t:real` `cD:real` THEN PBWCA_PROD_TAC `cB:real` `sD:real` THEN
  PBWCA_PROD_TAC `cD:real` `cB - t` THEN PBWCA_PROD_TAC `t:real` `cD - sD` THEN
  SUBGOAL_THEN `&0 <= (cB * cD - t * sD)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBWCA_USE C696PC_UPPER_PP
    [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `t:real`; `cB:real`] THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `ABT_upper c s u v a nx ny = e`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN
  PBWCA_PROD_TAC `t:real` `uD - (&2 * cD + sD / &2)` THEN
  PBWCA_PROD_TAC `(cB * cD - t * sD)` `sD * uD + cD * vD` THEN
  PBWCA_PRODLT_TAC `cD:real` `&1 + (t * cD + cB * sD) + (cB * cD - t * sD)` THEN
  PBWCA_PRODLT_TAC `aD - &1` `cD * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD))` THEN
  PBWCA_PROD_TAC `cD:real` `(&1 - cB * (&2 - cD - sD) - t * (&1 - cD + sD / &2))` THEN
  SUBGOAL_THEN `&0 <= t * sD` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PBWCA_PROD_TAC `t * sD` `&1 - cD` THEN
  SUBGOAL_THEN `&0 <= cD * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD) - &2 * cB - t) + t * sD / &2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBWCA_PROD_TAC `cD:real` `(&2 * cB + &3 * t) - (((t * cD + cB * sD) * (uD + aD) + (cB * cD - t * sD) * (vD + aD)) + aD)` THEN
  SUBGOAL_THEN
   `cD * (((t * cD + cB * sD) * (uD + aD) + (cB * cD - t * sD) * (vD + aD)) + aD - (&2 * cB + &3 * t)) =
    t * (uD - (&2 * cD + sD / &2)) + (cB * cD - t * sD) * (sD * uD + cD * vD) +
    (aD - &1) * (cD * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD))) + (cD * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD) - &2 * cB - t) + t * sD / &2)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: impossible *)
let PBWCA_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD cB (sB:real) (uB:real) vB aB t.
     c977cc_normal cO sO /\ c977cc_normal cD sD /\ c977cc_normal cB t /\
     aO = aD /\ aD = aB /\ &1 < aO /\
     vO + aO <= cO - sO /\ &0 <= sO * uO + cO * vO /\ lcont cD sD uD vD aD /\
     vB + aB <= &2 * cB + &3 * t /\
     (uO + aO <= ABT_lower cD sD uD vD aD cO sO \/ ABT_upper cO sO uO vO aO cD sD <= uD) /\
     ABT_upper cD sD uD vD aD t cB <= vB
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [ALL_TAC;
   PBWCA_USE PBS_POSITIVE_PROJECTION
     [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cD:real`; `sD:real`] THEN
   MATCH_MP_TAC PBWCA_OF_ENTRY THEN
   MAP_EVERY EXISTS_TAC [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                         `cB:real`; `vB:real`; `aB:real`; `t:real`] THEN
   REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC)] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aD`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aD:real = aB`)) THEN
  PBWCA_USE PBWCA_DISK [`cD:real`; `sD:real`; `cB:real`; `t:real`] THEN
  PBWCA_USE PBS_OWN_AXIS [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aD:real`] THEN
  PBWCA_NORMAL_TAC THEN
  SUBGOAL_THEN `cD * cD + sD * sD = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  SUBGOAL_THEN `abs sD = sD` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sD * uD + cD * vD` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PBWCA_PROD_TAC `t:real` `cD:real` THEN PBWCA_PROD_TAC `cB:real` `sD:real` THEN
  PBWCA_PROD_TAC `cD:real` `cB - t` THEN PBWCA_PROD_TAC `t:real` `cD - sD` THEN
  SUBGOAL_THEN `&0 <= (cB * cD - t * sD)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBWCA_PROD_TAC `cO:real` `cD:real` THEN PBWCA_PROD_TAC `sO:real` `sD:real` THEN
  PBWCA_USE C696PC_UPPER_PP
    [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `t:real`; `cB:real`] THEN
  PBWCA_USE PBWCA_LOWER_PM
    [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `cO:real`; `sO:real`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `--cO * sD + sO * cD = (sO * cD - cO * sD)`]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if can (term_match [] `ABT_upper c s u v a nx ny = e`) (concl th) ||
                                    can (term_match [] `ABT_lower c s u v a nx ny = e`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "")) THEN
  SUBGOAL_THEN `(min (sO * cD - cO * sD) (&0)) <= &0` ASSUME_TAC THENL
  [REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PBWCA_PROD_TAC `t:real` `((cO * cD + sO * sD) * uD + (sO * cD - cO * sD) * vD + aD * (min (sO * cD - cO * sD) (&0))) - (&2 * cO + sO / &2)` THEN
  PBWCA_PROD_TAC `cB:real` `cO - sO` THEN PBWCA_PROD_TAC `sO:real` `cB - t` THEN
  SUBGOAL_THEN `&0 <= (cO * cB - sO * t)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBWCA_PROD_TAC `(cO * cB - sO * t)` `sD * uD + cD * vD` THEN
  PBWCA_PRODLT_TAC `cO:real` `&1 + (t * cD + cB * sD) + (cB * cD - t * sD)` THEN
  PBWCA_PROD_TAC `t:real` `--((min (sO * cD - cO * sD) (&0)))` THEN
  SUBGOAL_THEN `&0 < (cO * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD)) - t * (min (sO * cD - cO * sD) (&0)))` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PBWCA_PRODLT_TAC `aD - &1` `(cO * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD)) - t * (min (sO * cD - cO * sD) (&0)))` THEN
  PBWCA_PROD_TAC `sO:real` `&1 - cD` THEN
  SUBGOAL_THEN `&0 <= sO / &2 - cO * sD / &2 - (min (sO * cD - cO * sD) (&0))` ASSUME_TAC THENL
  [REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBWCA_PROD_TAC `t:real` `sO / &2 - cO * sD / &2 - (min (sO * cD - cO * sD) (&0))` THEN
  PBWCA_PROD_TAC `cO:real` `(&1 - cB * (&2 - cD - sD) - t * (&1 - cD + sD / &2))` THEN
  SUBGOAL_THEN `&0 <= (cO * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD)) - t * (min (sO * cD - cO * sD) (&0))) + t * (&2 * cO + sO / &2) - cO * (&2 * cB + &3 * t)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBWCA_PROD_TAC `cO:real` `(&2 * cB + &3 * t) - (((t * cD + cB * sD) * (uD + aD) + (cB * cD - t * sD) * (vD + aD)) + aD)` THEN
  SUBGOAL_THEN
   `cO * (((t * cD + cB * sD) * (uD + aD) + (cB * cD - t * sD) * (vD + aD)) + aD - (&2 * cB + &3 * t)) =
    t * (((cO * cD + sO * sD) * uD + (sO * cD - cO * sD) * vD + aD * (min (sO * cD - cO * sD) (&0))) - (&2 * cO + sO / &2)) + (cO * cB - sO * t) * (sD * uD + cD * vD) + (aD - &1) * (cO * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD)) - t * (min (sO * cD - cO * sD) (&0))) +
    ((cO * (&1 + (t * cD + cB * sD) + (cB * cD - t * sD)) - t * (min (sO * cD - cO * sD) (&0))) + t * (&2 * cO + sO / &2) - cO * (&2 * cB + &3 * t))` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_bottom_wall_axis *)
let PBWCA_NEGATIVE_BOTTOM_WALL_AXIS = prove
 (`forall cO sO uO vO aO cD sD uD vD aD cB (sB:real) (uB:real) vB aB q t.
     sO = --q /\ c977cc_normal cO q /\ c977cc_normal cD sD /\ c977cc_normal cB t /\
     aO = aD /\ aD = aB /\ &1 < aO /\ cO - q <= uO /\ q * (uO + aO) <= cO * vO /\
     lcont cD sD uD vD aD /\ vB + aB <= &2 * cB + &3 * t /\
     ABT_upper cO sO uO vO aO cD sD <= uD /\ ABT_upper cD sD uD vD aD t cB <= vB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PBWCA_USE PBS_NEGATIVE_FRAME_PROJECTION
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `q:real`; `cD:real`; `sD:real`] THEN
  MATCH_MP_TAC PBWCA_OF_ENTRY THEN
  MAP_EVERY EXISTS_TAC [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                        `cB:real`; `vB:real`; `aB:real`; `t:real`] THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC));;
