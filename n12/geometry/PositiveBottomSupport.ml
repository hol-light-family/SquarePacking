(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveBottomSupport.lean (Jatloe, N12-jatloe)  *)
(* (namespace N12Compact.PositiveBottomSupport).                             *)
(* Bottom containment and the missing-corner face give a uniform positive-   *)
(* direction support.  Lean upper is ABT_upper.                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/PositiveBottomNextAxes.ml";;

let PBS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PBS_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PBS_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PBS_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PBS_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let PBS_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: positive_projection *)
let PBS_POSITIVE_PROJECTION = prove
 (`forall cO sO uO vO aO d r.
     c977cc_normal cO sO /\ c977cc_normal d r /\ &1 < aO /\
     vO + aO <= cO - sO /\ &0 <= sO * uO + cO * vO
     ==> &2 * d + r / &2 < ABT_upper cO sO uO vO aO d r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PBS_NORMAL_TAC THEN
  PBS_PRODLT_TAC `d:real` `cO:real` THEN PBS_PROD_TAC `r:real` `sO:real` THEN
  SUBGOAL_THEN `&0 < (d * cO + r * sO)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PBS_PROD_TAC `&1 - cO` `sO - (&1 - cO) / &2` THEN
  PBS_PROD_TAC `d:real` `(&1 - cO) * (sO - (&1 - cO) / &2)` THEN
  PBS_PROD_TAC `(d * cO + r * sO)` `sO * uO + cO * vO` THEN
  PBS_PROD_TAC `d:real` `(cO - sO) - (vO + aO)` THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PBS_POS_OF_MUL THEN
  EXISTS_TAC `sO:real` THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (r * cO - d * sO)` THENL
  [PBS_USE C696PC_UPPER_PP
     [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `d:real`; `r:real`] THEN
   FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match [] `ABT_upper c s u v a nx ny = e`) o concl)) THEN
   PBS_PROD_TAC `sO:real` `cO + sO - &1 / &2` THEN
   PBS_PROD_TAC `(r * cO - d * sO)` `sO * (cO + sO - &1 / &2)` THEN
   SUBGOAL_THEN `cO * (--d * (&1 - cO) * (cO + sO) + r * sO * (cO + sO - &1 / &2)) = d * (&1 - cO) * (sO - (&1 - cO) / &2) +
                 (r * cO - d * sO) * sO * (cO + sO - &1 / &2)` ASSUME_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (--d * (&1 - cO) * (cO + sO) + r * sO * (cO + sO - &1 / &2))` ASSUME_TAC THENL
   [MATCH_MP_TAC PBS_NONNEG_OF_MUL THEN EXISTS_TAC `cO:real` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   PBS_PRODLT_TAC `(d * cO + r * sO)` `cO + sO` THEN
   PBS_PRODLT_TAC `aO - &1` `(d * cO + r * sO) * (cO + sO)` THEN
   SUBGOAL_THEN `sO * (((d * cO + r * sO) * (uO + aO) + (--d * sO + r * cO) * (vO + aO)) - (&2 * d + r / &2)) =
     (d * cO + r * sO) * (sO * uO + cO * vO) + d * (cO - sO - (vO + aO)) +
     (aO - &1) * ((d * cO + r * sO) * (cO + sO)) + (--d * (&1 - cO) * (cO + sO) + r * sO * (cO + sO - &1 / &2))` ASSUME_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  PBS_USE PBNA_UPPER_PN
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `d:real`; `r:real`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match [] `ABT_upper c s u v a nx ny = e`) o concl)) THEN
  SUBGOAL_THEN `&0 <= (d * (&1 - cO) * (&1 - sO) + r * sO * (sO - &1 / &2))` ASSUME_TAC THENL
  [ASM_CASES_TAC `&1 / &2 <= sO` THENL
   [PBS_PROD_TAC `&1 - cO` `&1 - sO` THEN
    PBS_PROD_TAC `d:real` `(&1 - cO) * (&1 - sO)` THEN
    PBS_PROD_TAC `r * sO` `sO - &1 / &2` THEN RASM_ARITH_TAC;
    PBS_PROD_TAC `sO:real` `&1 / &2 - sO` THEN
    PBS_PROD_TAC `--(r * cO - d * sO)` `sO * (&1 / &2 - sO)` THEN
    SUBGOAL_THEN `cO * (d * (&1 - cO) * (&1 - sO) + r * sO * (sO - &1 / &2)) = d * (&1 - cO) * (sO - (&1 - cO) / &2) +
                  (r * cO - d * sO) * sO * (sO - &1 / &2)` ASSUME_TAC THENL
    [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC PBS_NONNEG_OF_MUL THEN EXISTS_TAC `cO:real` THEN
    CONJ_TAC THEN RASM_ARITH_TAC]; ALL_TAC] THEN
  PBS_PROD_TAC `sO:real` `(d * cO + r * sO)` THEN
  PBS_PRODLT_TAC `aO - &1` `d + sO * (d * cO + r * sO)` THEN
  SUBGOAL_THEN `sO * (((d * cO + r * sO) * (uO + aO) + (--d * sO + r * cO) * vO) - (&2 * d + r / &2)) =
    (d * cO + r * sO) * (sO * uO + cO * vO) + d * (cO - sO - (vO + aO)) +
    (aO - &1) * (d + sO * (d * cO + r * sO)) + (d * (&1 - cO) * (&1 - sO) + r * sO * (sO - &1 / &2))` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: own_axis *)
let PBS_OWN_AXIS = prove
 (`forall cO sO uO vO aO.
     c977cc_normal cO sO /\ &1 < aO /\ vO + aO <= cO - sO /\ &0 <= sO * uO + cO * vO
     ==> &2 * cO + sO / &2 < uO + aO`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PBS_USE PBS_POSITIVE_PROJECTION
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cO:real`; `sO:real`] THEN
  PBS_NORMAL_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] ABT_OWNU) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; RASM_ARITH_TAC];
   STRIP_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_frame_projection *)
let PBS_NEGATIVE_FRAME_PROJECTION = prove
 (`forall cO sO uO vO aO t d r.
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal d r /\ &1 < aO /\
     cO - t <= uO /\ t * (uO + aO) <= cO * vO
     ==> &2 * d + r / &2 < ABT_upper cO sO uO vO aO d r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PBS_NORMAL_TAC THEN
  PBS_PROD_TAC `cO:real` `d - r` THEN PBS_PROD_TAC `r:real` `cO - t` THEN
  SUBGOAL_THEN `&0 <= d * cO - r * t` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBS_PROD_TAC `d:real` `t:real` THEN PBS_PROD_TAC `r:real` `cO:real` THEN
  PBS_USE C977NCO_UPPER_NEGATIVE_POS
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `t:real`; `d:real`; `r:real`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match [] `ABT_upper c s u v a nx ny = e`) o concl)) THEN
  PBS_PROD_TAC `d:real` `uO - (cO - t)` THEN
  PBS_PROD_TAC `d * t + r * cO` `cO * vO - t * (uO + aO)` THEN
  PBS_PROD_TAC `cO:real` `d * t + r * cO` THEN
  PBS_PRODLT_TAC `aO - &1` `d + cO * (d * t + r * cO)` THEN
  PBS_PROD_TAC `&1 - cO` `&1 - t` THEN
  PBS_PROD_TAC `d:real` `(&1 - cO) * (&1 - t)` THEN
  PBS_PROD_TAC `r * cO` `cO - &1 / &2` THEN
  SUBGOAL_THEN
   `cO * (((d * cO - r * t) * (uO + aO) + (d * t + r * cO) * (vO + aO)) - (&2 * d + r / &2)) =
    d * (uO - (cO - t)) + (d * t + r * cO) * (cO * vO - t * (uO + aO)) +
    (aO - &1) * (d + cO * (d * t + r * cO)) + d * (&1 - cO) * (&1 - t) +
    r * cO * (cO - &1 / &2)` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PBS_POS_OF_MUL THEN
  EXISTS_TAC `cO:real` THEN CONJ_TAC THEN RASM_ARITH_TAC);;
