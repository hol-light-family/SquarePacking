(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralNegativeFloor.lean (Jatloe,       *)
(* N12-jatloe; namespace N12Compact.PositiveCentralNegativeFloor).           *)
(* The surviving negative-bottom separator gives a horizontal support bound  *)
(* for the positive central square.  Lean lower is ABT_lower.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/PositiveCentralNegativeBottom.ml";;

let PCNF_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCNF_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PCNF_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCNF_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PCNF_LOWER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_lower c s u v a nx ny = (nx * c + ny * s) * u + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC);;

let PCNF_POS_BY_POS = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: boundary_margin (private) *)
let PCNF_BOUNDARY_MARGIN = prove
 (`forall c t. c977cc_normal c t ==> c + (&8 / &5) * t <= c977cc_boundary c t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PCNF_NORMAL_TAC THEN
  PCNF_PROD_TAC `c + t - &1` `&3 / &2 - (c + t)` THEN
  PCNF_PROD_TAC `c:real` `t:real` THEN
  NLIN_FACTS_TAC [] [`(&4 / &5) * c * t <= c + t - &1`] THEN
  SUBGOAL_THEN `c * c977cc_boundary c t = c + c * t + t - t pow 2` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_boundary] THEN
   (SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false []);;

(* Lean: of_separation *)
let PCNF_OF_SEPARATION = prove
 (`forall cO (sO:real) (uO:real) vO aO cA sA uA vA aA t.
     c977cc_normal cO t /\ c977cc_normal cA sA /\ &1 <= aA /\
     uA + aA <= &2 * (cA + sA) /\ c977cc_boundary cO t < vO + aO /\
     vO + aO <= ABT_lower cA sA uA vA aA t cO
     ==> &1 < ABT_lower cA sA uA vA aA (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCNF_USE PCNF_BOUNDARY_MARGIN [`cO:real`; `t:real`] THEN PCNF_NORMAL_TAC THEN
  PCNF_PROD_TAC `cO:real` `cA - sA` THEN
  PCNF_PROD_TAC `sA:real` `cO - t` THEN
  SUBGOAL_THEN `&0 <= cO * cA - t * sA` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCNF_PROD_TAC `t:real` `cA:real` THEN PCNF_PROD_TAC `cO:real` `sA:real` THEN
  PCNF_USE PCNF_LOWER_PP
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `&0`; `&1`] THEN
  PCNF_USE PCNF_LOWER_PP
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `t:real`; `cO:real`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sA * uA + cA * vA <= &1` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCNF_PROD_TAC `cO * cA - t * sA` `&1 - (sA * uA + cA * vA)` THEN
  PCNF_PROD_TAC `t:real` `&2 * (cA + sA) - &1 - uA` THEN
  SUBGOAL_THEN
   `cA * ((t * cA + cO * sA) * uA + (--t * sA + cO * cA) * vA) =
    t * uA + (cO * cA - t * sA) * (sA * uA + cA * vA)` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCNF_PROD_TAC `t:real` `&1 - (sA + (&2 / &5) * cA)` THEN
  PCNF_PROD_TAC `cA:real` `c977cc_boundary cO t - (cO + (&8 / &5) * t)` THEN
  SUBGOAL_THEN `cA * c977cc_boundary cO t < cA * ABT_lower cA sA uA vA aA t cO`
  MP_TAC THENL [MATCH_MP_TAC REAL_LT_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th =
    `ABT_lower cA sA uA vA aA t cO = (t * cA + cO * sA) * uA + (--t * sA + cO * cA) * vA`)) THEN
  DISCH_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: actual *)
let PCNF_ACTUAL = prove
 (`forall cO sO uO vO aO cA sA uA vA aA t.
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cA sA /\
     &1 < aO /\ &1 <= aA /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     uA + aA <= &2 * (cA + sA) /\
     vO + aO <= ABT_lower cA sA uA vA aA t cO
     ==> &1 < ABT_lower cA sA uA vA aA (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCNF_USE C977NCO_CORNER_FACE [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `t:real`] THEN
  MATCH_MP_TAC PCNF_OF_SEPARATION THEN
  MAP_EVERY EXISTS_TAC [`cO:real`; `vO:real`; `aO:real`; `t:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: inner_left_point *)
let PCNF_INNER_LEFT_POINT = prove
 (`forall c s u v a. c977cc_normal c s /\ &1 < a /\ u + a <= &2 * (c + s) /\
     &1 < s * u + c * v /\
     linside c s u v a (&33 / &20) (&33 / &20) /\ linside c s u v a (&3 / &2) (&2)
     ==> linside c s u v a (&6 / &5) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCNF_NORMAL_TAC THEN
  PCNF_PROD_TAC `c + s - &1` `&3 / &2 - (c + s)` THEN
  NLIN_FACTS_TAC [] [`&0 <= c + s - &1 - (&4 / &5) * c * s`] THEN
  PCNF_PROD_TAC `s:real` `&2 * (c + s) - (u + a)` THEN
  PCNF_PRODLT_TAC `c + s` `a - &1` THEN
  SUBGOAL_THEN
   `c * (v + a - (&2 * c - (&6 / &5) * s)) =
    (s * u + c * v - &1) + s * (&2 * (c + s) - a - u) + (c + s) * (a - &1) +
    (c + s - &1 - (&4 / &5) * c * s)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * c - (&6 / &5) * s < v + a` ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PCNF_POS_BY_POS THEN
   EXISTS_TAC `c:real` THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ASSUME `linside c s u v a (&33 / &20) (&33 / &20)`) THEN
  MP_TAC(ASSUME `linside c s u v a (&3 / &2) (&2)`) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: left_support *)
let PCNF_LEFT_SUPPORT = prove
 (`forall c s u v a. c977cc_normal c s /\ &1 < a /\ u + a <= &2 * (c + s) /\
     &1 <= s * u + c * v
     ==> c * u - s * (v + a) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCNF_NORMAL_TAC THEN
  PCNF_PROD_TAC `c:real` `s:real` THEN
  PCNF_PRODLT_TAC `a - &1` `&1 + c * s` THEN
  PCNF_PROD_TAC `&1 - c` `&1 - s` THEN
  PCNF_PROD_TAC `s:real` `(s * u + c * v) - &1` THEN
  SUBGOAL_THEN
   `c * (&1 - (c * u - s * (v + a))) =
    (&2 * (c + s) - a - u) + s * (s * u + c * v - &1) +
    (a - &1) * (&1 + c * s) + (&1 - c) * (&1 - s)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PCNF_POS_BY_POS THEN
  EXISTS_TAC `c:real` THEN CONJ_TAC THEN RASM_ARITH_TAC);;
