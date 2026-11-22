(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveAngleOrder.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveAngleOrder).          *)
(* The quadratic A/R clearance orders the opposite central frames below the  *)
(* upper outer frame.  Normal is c977cc_normal; upper/lower are ABT_upper/   *)
(* ABT_lower; lower_pp: FAWTE_LOWER_PP; closed_bounds: ABT_CLOSED_BOUNDS;    *)
(* FullAuxWallPositiveOpposite.central_v_band: FAWPO_CENTRAL_V_BAND;         *)
(* dot_le_one: C977CSB_DOT_LE_ONE.  The OpenSquare invariants are explicit.  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_C981_NegativePoint.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FullAuxWallPositiveOpposite.ml";;
needs "n12/geometry/FullAuxWallPositiveTop.ml";;

let FAWPAO_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPAO_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let FAWPAO_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let FAWPAO_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
           filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
         CONV_TAC REAL_RING];;

let FAWPAO_USE th tms =
  MP_TAC(SPECL tms th) THEN ANTS_TAC THENL [FAWPAO_ANTS_TAC; DISCH_THEN STRIP_ASSUME_TAC];;

(* Lean: bands_closed (private) *)
let FAWPAO_BANDS_CLOSED = prove
 (`forall c s u v a p q. c * c + s * s = &1 /\ u <= p /\ p <= u + a /\ v <= q /\ q <= v + a
     ==> lclosed c s u v a (c * p - s * q) (s * p + c * q)`,
  ACCEPT_TAC FAWPO_BANDS_CLOSED);;

(* Lean: projected_excess *)
let FAWPAO_PROJECTED_EXCESS = prove
 (`forall cA sA uA vA aA cD sD uD vD aD.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     c977cc_normal cA sA /\ c977cc_normal cD sD /\
     &1 < aA /\ &0 < sA /\ &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&2) (&2) /\
     (ABT_upper cD sD uD vD aD cA sA <= uA \/
      uD + aD <= ABT_lower cA sA uA vA aA cD sD)
     ==> (cA * cD + sA * sD) * (uD + aD - &2 * (cD + sD)) <= uA - &2 * (cA + sA)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FAWPAO_USE C977CSB_DOT_LE_ONE [`cA:real`; `sA:real`; `cD:real`; `sD:real`] THEN
  FAWPAO_NORMAL_TAC THEN
  FAWPAO_PRODLT_TAC `cA:real` `cD:real` THEN FAWPAO_PROD_TAC `sA:real` `sD:real` THEN
  MP_TAC(ASSUME `linside cD sD uD vD aD (&2) (&2)`) THEN REWRITE_TAC[linside] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [FAWPAO_USE FAWPAO_BANDS_CLOSED [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
     `uD + aD:real`; `&2 * (cD - sD)`] THEN
   FAWPAO_USE ABT_CLOSED_BOUNDS [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
     `cD * (uD + aD) - sD * (&2 * (cD - sD))`; `sD * (uD + aD) + cD * (&2 * (cD - sD))`;
     `cA:real`; `sA:real`] THEN
   SUBGOAL_THEN
    `cA * (cD * (uD + aD) - sD * (&2 * (cD - sD))) +
     sA * (sD * (uD + aD) + cD * (&2 * (cD - sD))) - &2 * (cA + sA) =
     (cA * cD + sA * sD) * (uD + aD - &2 * (cD + sD))` ASSUME_TAC THENL
   [UNDISCH_TAC `cD * cD + sD * sD = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  FAWPAO_USE FAWPO_CENTRAL_V_BAND [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  FAWPAO_USE FAWPAO_BANDS_CLOSED [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
    `uA:real`; `&2 * (cA - sA)`] THEN
  FAWPAO_USE ABT_CLOSED_BOUNDS [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
    `cA * uA - sA * (&2 * (cA - sA))`; `sA * uA + cA * (&2 * (cA - sA))`;
    `cD:real`; `sD:real`] THEN
  SUBGOAL_THEN
   `cD * (cA * uA - sA * (&2 * (cA - sA))) + sD * (sA * uA + cA * (&2 * (cA - sA))) -
    &2 * (cD + sD) = (cA * cD + sA * sD) * (uA - &2 * (cA + sA))` ASSUME_TAC THENL
  [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `uD + aD - &2 * (cD + sD) <= (cA * cD + sA * sD) * (uA - &2 * (cA + sA))`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FAWPAO_PROD_TAC `cA * cD + sA * sD`
    `(cA * cD + sA * sD) * (uA - &2 * (cA + sA)) - (uD + aD - &2 * (cD + sD))` THEN
  FAWPAO_PROD_TAC `&1 - (cA * cD + sA * sD)` `&1 + (cA * cD + sA * sD)` THEN
  FAWPAO_PROD_TAC `uA - &2 * (cA + sA)`
    `(&1 - (cA * cD + sA * sD)) * (&1 + (cA * cD + sA * sD))` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: small_excess *)
let FAWPAO_SMALL_EXCESS = prove
 (`forall cA sA uA vA aA cD sD uD vD aD.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     c977cc_normal cA sA /\ c977cc_normal cD sD /\
     &1 < aA /\ &0 < sA /\ &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     uA - &2 * (cA + sA) < sA pow 2 / &10 /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&2) (&2) /\
     (ABT_upper cD sD uD vD aD cA sA <= uA \/
      uD + aD <= ABT_lower cA sA uA vA aA cD sD)
     ==> uD + aD - &2 * (cD + sD) < &1 / &112`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`]
    FAWPAO_PROJECTED_EXCESS) THEN
  ANTS_TAC THENL [FAWPAO_ANTS_TAC; DISCH_TAC] THEN
  FAWPAO_NORMAL_TAC THEN
  FAWPAO_PROD_TAC `cA:real` `cD - &7 / &10` THEN FAWPAO_PROD_TAC `sA:real` `sD:real` THEN
  SUBGOAL_THEN `(&7 / &10) * cA <= cA * cD + sA * sD` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPAO_PROD_TAC `cA - &4 * sA` `sA:real` THEN
  FAWPAO_PROD_TAC `cA:real` `&1 - &4 * sA` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FAWPAO_PROD_TAC `(cA * cD + sA * sD) - (&7 / &10) * cA` `uD + aD - &2 * (cD + sD)` THEN
  FAWPAO_PROD_TAC `cA:real` `(uD + aD - &2 * (cD + sD)) - &1 / &112` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: slope_scalar (private) *)
let FAWPAO_SLOPE_SCALAR = prove
 (`forall c s C S. c977cc_normal c s /\ c977cc_normal C S /\ &0 < s /\ &4 * s <= c /\
     (C * (c * S - s * C) / &2 < s pow 2 / &5 \/
      &0 < (c * C + s * S) * (s pow 2 / &5) + (c * S - s * C) * (c - &1 - (&2 / &5) * s))
     ==> &82 * S < &29 * C`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FAWPAO_NORMAL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FAWPAO_PRODLT_TAC `c:real` `C:real` THEN FAWPAO_PROD_TAC `s:real` `S:real` THEN
  FAWPAO_PROD_TAC `c - &4 * s` `&21 * C + &2 * S` THEN
  FAWPAO_PROD_TAC `c:real` `&82 * S - &29 * C` THEN
  SUBGOAL_THEN `(&2 / &21) * (c * C + s * S) <= c * S - s * C` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * S - s * C` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [FAWPAO_PROD_TAC `c:real` `C - &7 / &10` THEN
   SUBGOAL_THEN `(&7 / &10) * c <= c * C + s * S` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   FAWPAO_PROD_TAC `C - &7 / &10` `c * S - s * C` THEN
   FAWPAO_PROD_TAC `c - &4 * s` `s:real` THEN
   FAWPAO_PROD_TAC `c:real` `&1 - &4 * s` THEN
   NLIN_TAC ~deg2:false [];
   SUBGOAL_THEN `c - &1 <= --(s pow 2) / &2` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - &1`]; ALL_TAC] THEN
   FAWPAO_PROD_TAC `c * S - s * C` `--(c - &1 + s pow 2 / &2)` THEN
   SUBGOAL_THEN `&0 <= (&2 / &5) * s + s pow 2 / &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN RASM_ARITH_TAC; ALL_TAC] THEN
   FAWPAO_PROD_TAC `(c * S - s * C) - (&2 / &21) * (c * C + s * S)`
     `(&2 / &5) * s + s pow 2 / &2` THEN
   FAWPAO_PROD_TAC `c * C + s * S` `s:real` THEN
   FAWPAO_PROD_TAC `(c * C + s * S) * s` `&1 - &4 * s` THEN
   NLIN_TAC ~deg2:false []]);;

(* Lean: upper_pn (private) *)
let FAWPAO_UPPER_PN = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ --x * s + y * c <= &0
     ==> ABT_upper c s u v a x y = (x * c + y * s) * (u + a) + (--x * s + y * c) * v`,
  REPEAT STRIP_TAC THEN C981NP_FORM_TAC);;

(* Lean: opposite_slope_strong *)
let FAWPAO_OPPOSITE_SLOPE_STRONG = prove
 (`forall cA sA uA vA aA cD sD uD vD aD.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     c977cc_normal cA sA /\ c977cc_normal cD sD /\
     &1 < aA /\ &0 < sA /\ &4 * sA <= cA /\
     uA - &2 * (cA + sA) < sA pow 2 / &5 /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&2) (&2) /\ linside cD sD uD vD aD (&2) (&3 / &2) /\
     (ABT_upper cD sD uD vD aD cA sA <= uA \/
      uD + aD <= ABT_lower cA sA uA vA aA cD sD)
     ==> &82 * sD < &29 * cD`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FAWPAO_NORMAL_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cD sD uD vD aD (&2) (&2)`; `linside cD sD uD vD aD (&2) (&3 / &2)`] THEN
  ASM_CASES_TAC `cA * sD <= sA * cD` THENL
  [FAWPAO_PROD_TAC `cD:real` `cA - &4 * sA` THEN
   SUBGOAL_THEN `&4 * sD <= cD` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FAWPAO_PRODLT_TAC `cA:real` `&4 * sD - cD` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  FAWPAO_PRODLT_TAC `cA:real` `cD:real` THEN FAWPAO_PROD_TAC `sA:real` `sD:real` THEN
  MATCH_MP_TAC FAWPAO_SLOPE_SCALAR THEN EXISTS_TAC `cA:real` THEN EXISTS_TAC `sA:real` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [DISJ1_TAC THEN
   MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `cA:real`; `sA:real`]
     FAWPAO_UPPER_PN) THEN
   ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
   SUBGOAL_THEN `ABT_upper cD sD uD vD aD cA sA - &2 * (cA + sA) =
                 (cA * cD + sA * sD) * (uD + aD - &2 * (cD + sD)) +
                 (cA * sD - sA * cD) * (&2 * (cD - sD) - vD)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cD * cD + sD * sD = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   FAWPAO_PRODLT_TAC `cA * sD - sA * cD` `(&2 * (cD - sD) - vD) - cD / &2` THEN
   FAWPAO_PRODLT_TAC `cA * cD + sA * sD` `uD + aD - &2 * (cD + sD)` THEN
   NLIN_TAC ~deg2:false [];
   DISJ2_TAC THEN
   MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `cD:real`; `sD:real`]
     FAWTE_LOWER_PP) THEN
   ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
   SUBGOAL_THEN `ABT_lower cA sA uA vA aA cD sD - &2 * (cD + sD) =
                 (cA * cD + sA * sD) * (uA - &2 * (cA + sA)) +
                 (cA * sD - sA * cD) * (vA - &2 * (cA - sA))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cA * cA + sA * sA = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   FAWPAO_PRODLT_TAC `cA * cD + sA * sD` `sA pow 2 / &5 - (uA - &2 * (cA + sA))` THEN
   FAWPAO_PRODLT_TAC `cA * sD - sA * cD` `(cA - &1 - (&2 / &5) * sA) - (vA - &2 * (cA - sA))` THEN
   NLIN_TAC ~deg2:false []]);;

(* Lean: outer_slope_strong *)
let FAWPAO_OUTER_SLOPE_STRONG = prove
 (`forall b t. c977cc_normal b t /\ &1 < (&343 / &500) * b + t ==> &77 * b < &200 * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPAO_NORMAL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FAWPAO_PROD_TAC `b:real` `&77 * b - &200 * t` THEN
  FAWPAO_PRODLT_TAC `(&343 / &500) * b + t - &1` `(&343 / &500) * b + t + &1` THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `b:real`]);;

(* Lean: outer_slope *)
let FAWPAO_OUTER_SLOPE = prove
 (`forall b t. c977cc_normal b t /\ &1 < (&343 / &500) * b + t ==> &9 * b < &25 * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] FAWPAO_OUTER_SLOPE_STRONG) THEN
  ASM_REWRITE_TAC[] THEN FAWPAO_NORMAL_TAC THEN RASM_ARITH_TAC);;

(* Lean: ordered *)
let FAWPAO_ORDERED = prove
 (`forall C S b t. c977cc_normal C S /\ c977cc_normal b t /\ &25 * S < &9 * C /\
     &1 < (&343 / &500) * b + t ==> b * S < t * C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] FAWPAO_OUTER_SLOPE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FAWPAO_NORMAL_TAC THEN
  FAWPAO_PRODLT_TAC `b:real` `&9 * C - &25 * S` THEN
  FAWPAO_PRODLT_TAC `C:real` `&25 * t - &9 * b` THEN
  NLIN_TAC ~deg2:false []);;
