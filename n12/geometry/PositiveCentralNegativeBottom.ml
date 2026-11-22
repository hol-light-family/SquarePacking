(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralNegativeBottom.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.PositiveCentralNegativeBottom).          *)
(* A negative canonical bottom square cannot separate from the central       *)
(* square on the central transverse axis.  Lean upper is ABT_upper; a square *)
(* with O.s = -t is cO sO uO vO aO with the hypothesis sO = --t.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let PCNB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCNB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PCNB_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCNB_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: coefficient_bound (private) *)
let PCNB_COEFFICIENT_BOUND = prove
 (`forall c t C S. c977cc_normal c t /\ c977cc_normal C S
     ==> c * (&2 - c - t) * C + t * (c + t - &457 / &500) * S <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCNB_NORMAL_TAC THEN
  ASM_CASES_TAC `t <= &9 / &20` THENL
  [PCNB_PROD_TAC `c:real` `&2 - c - t` THEN
   PCNB_PROD_TAC `t:real` `c + t - &457 / &500` THEN
   PCNB_PROD_TAC `t:real` `&457 / &500 - &2 * t` THEN
   SUBGOAL_THEN `c * (&2 - c - t) + t * (c + t - &457 / &500) <= c` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PCNB_PROD_TAC `c * (&2 - c - t)` `&1 - C` THEN
   PCNB_PROD_TAC `t * (c + t - &457 / &500)` `&1 - S` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  PCNB_PROD_TAC `c:real` `&17 / &20 - (&2 - c - t)` THEN
  PCNB_PROD_TAC `t:real` `&13 / &25 - (c + t - &457 / &500)` THEN
  PCNB_PROD_TAC `c - t` `&13 / &25` THEN
  SUBGOAL_THEN `c * (&2 - c - t) <= (&17 / &20) * c /\
                t * (c + t - &457 / &500) <= (&13 / &25) * c` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C - &17 / &20`; SQ_NONNEG `S - &13 / &25`]
    [`(&17 / &20) * C + (&13 / &25) * S < &1`] THEN
  PCNB_PROD_TAC `C:real` `(&17 / &20) * c - c * (&2 - c - t)` THEN
  PCNB_PROD_TAC `S:real` `(&13 / &25) * c - t * (c + t - &457 / &500)` THEN
  PCNB_PRODLT_TAC `c:real` `&1 - ((&17 / &20) * C + (&13 / &25) * S)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: upper_axis *)
let PCNB_UPPER_AXIS = prove
 (`forall cO sO uO vO aO t C S.
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal C S /\ &1 < aO /\
     lcont cO sO uO vO aO /\ linside cO sO uO vO aO (&1) (&457 / &500)
     ==> &2 * C - S < ABT_upper cO sO uO vO aO (--S) C + aO`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCNB_USE PCNB_COEFFICIENT_BOUND [`cO:real`; `t:real`; `C:real`; `S:real`] THEN
  PCNB_NORMAL_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --t`)) THEN
  SUBGOAL_THEN `cO * cO + --t * --t = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aO:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy; REAL_ABS_NEG]) THEN
  SUBGOAL_THEN `abs t = t` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `t * (uO + aO) <= cO * vO` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cO (--t) uO vO aO (&1) (&457 / &500)`) THEN
  REWRITE_TAC[C977NCO_NEG_BANDS] THEN STRIP_TAC THEN
  PCNB_PROD_TAC `cO:real` `C - S` THEN
  PCNB_PROD_TAC `S:real` `cO - t` THEN
  SUBGOAL_THEN `&0 <= cO * C - t * S` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cO * S + t * C` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  PCNB_USE C977NCO_UPPER_NEGATIVE_NONPOS
    [`cO:real`; `--t`; `uO:real`; `vO:real`; `aO:real`; `t:real`; `--S`; `C:real`] THEN
  PCNB_PROD_TAC `cO * C - t * S` `cO + t` THEN
  PCNB_PROD_TAC `cO * C - t * S` `cO * vO - t * (uO + aO)` THEN
  PCNB_PROD_TAC `S:real` `cO - (&457 / &500) * t - uO` THEN
  PCNB_PRODLT_TAC `(cO * C - t * S) * (cO + t) + cO` `aO - &1` THEN
  SUBGOAL_THEN
   `cO * ((((--S) * cO - C * t) * uO + ((--S) * t + C * cO) * (vO + aO)) + aO -
          (&2 * C - S)) =
    (cO * C - t * S) * (cO * vO - t * (uO + aO)) +
    S * (cO - (&457 / &500) * t - uO) +
    ((cO * C - t * S) * (cO + t) + cO) * (aO - &1) +
    (cO - (cO * (&2 - cO - t) * C + t * (cO + t - &457 / &500) * S))` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match [] `ABT_upper c s u v a nx ny = e`) o concl)) THEN
  MATCH_MP_TAC C977CSUP_LT_BY_POS THEN EXISTS_TAC `cO:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: central_axis_impossible *)
let PCNB_CENTRAL_AXIS_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cA sA (uA:real) vA aA t.
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cA sA /\ aO = aA /\
     &1 < aA /\ lcont cO sO uO vO aO /\ linside cO sO uO vO aO (&1) (&457 / &500) /\
     vA + aA <= &2 * cA - sA
     ==> ~(ABT_upper cO sO uO vO aO (--sA) cA <= vA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCNB_USE PCNB_UPPER_AXIS [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `t:real`;
                `cA:real`; `sA:real`] THEN
  RASM_ARITH_TAC);;
