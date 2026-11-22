(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveReach.lean (Jatloe,           *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveReach).               *)
(* A true shifted left point of the positive opposite central square.        *)
(* Normal is c977cc_normal; lower/upper are ABT_lower/ABT_upper;             *)
(* FullAuxWallPositiveMargins.F/G/margin are fawpm_f/fawpm_g/FAWPM_MARGIN.   *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallPositiveOpposite.ml";;
needs "n12/geometry/FullAuxWallPositiveMargins.ml";;

let FAWPR_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPR_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let FAWPR_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let FAWPR_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: face (private) *)
let FAWPR_FACE = prove
 (`forall c s u v a p q. c * c + s * s = &1 /\ u <= p /\ p <= u + a /\ v <= q /\ q <= v + a
     ==> lclosed c s u v a (c * p - s * q) (s * p + c * q)`,
  ACCEPT_TAC FAWPO_BANDS_CLOSED);;

(* Lean: own_margin (private) *)
let FAWPR_OWN_MARGIN = prove
 (`forall c s C S. c977cc_normal c s /\ c977cc_normal C S /\ &4 * s <= c
     ==> (&13 / &50) * s <= (c * C + s * S) * (&1 - (&2 / &5) * C - S) +
                            (&1 / &2) * C * (c * S - s * C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPR_NORMAL_TAC THEN
  SUBGOAL_THEN `C * S <= &1 / &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `C - S:real`]; ALL_TAC] THEN
  FAWPR_PROD_TAC `C - &7 / &10` `&18 / &25 - (&2 / &5) * C` THEN
  SUBGOAL_THEN `&1 / &4 <= C * (&1 - (&2 / &5) * C - (&1 / &2) * S)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - (&2 / &5) * C - (&1 / &2) * S` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  FAWPR_PROD_TAC `c:real` `C * (&1 - (&2 / &5) * C - (&1 / &2) * S) - &1 / &4` THEN
  FAWPR_PROD_TAC `s:real` `S:real` THEN
  FAWPR_PROD_TAC `s * S` `&1 - (&2 / &5) * C - (&1 / &2) * S` THEN
  SUBGOAL_THEN
   `(c * C + s * S) * (&1 - (&2 / &5) * C - S) + (&1 / &2) * C * (c * S - s * C) =
    (c * C + s * S) * (&1 - (&2 / &5) * C - (&1 / &2) * S) - (&1 / &2) * s`
   ASSUME_TAC THENL
  [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: bottom_u *)
let FAWPR_BOTTOM_U = prove
 (`forall cA sA uA vA aA cD sD uD vD aD.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     &1 < aA /\ &1 < aD /\ c977cc_normal cA sA /\ c977cc_normal cD sD /\
     &0 < sA /\ &4 * sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&2) (&3 / &2) /\
     (ABT_upper cD sD uD vD aD cA sA <= uA \/
      uD + aD <= ABT_lower cA sA uA vA aA cD sD)
     ==> uD < (&8 / &5) * cD + sD`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FAWPR_NORMAL_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cA sA uA vA aA (&2) (&113 / &50)`; `linside cA sA uA vA aA (&5 / &2) (&3)`;
    `linside cD sD uD vD aD (&2) (&3 / &2)`] THEN
  FAWPR_PRODLT_TAC `cA:real` `cD:real` THEN FAWPR_PROD_TAC `sA:real` `sD:real` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FAWPR_USE FAWPR_FACE [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
     `uD + aD:real`; `--(&2) * sD + (&3 / &2) * cD`] THEN
   FAWPR_USE ABT_CLOSED_BOUNDS [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
     `cD * (uD + aD) - sD * (--(&2) * sD + (&3 / &2) * cD)`;
     `sD * (uD + aD) + cD * (--(&2) * sD + (&3 / &2) * cD)`; `cA:real`; `sA:real`] THEN
   SUBGOAL_THEN
    `cA * (cD * (uD + aD) - sD * (--(&2) * sD + (&3 / &2) * cD)) +
     sA * (sD * (uD + aD) + cD * (--(&2) * sD + (&3 / &2) * cD)) - &2 * (cA + sA) =
     (cA * cD + sA * sD) * (uD + aD - &2 * (cD + sD)) +
     (&1 / &2) * cD * (cA * sD - sA * cD)` ASSUME_TAC THENL
   [UNDISCH_TAC `cD * cD + sD * sD = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   FAWPR_PRODLT_TAC `cA * cD + sA * sD`
     `(uD + aD - &2 * (cD + sD)) - (&1 - (&2 / &5) * cD - sD)` THEN
   FAWPR_USE FAWPR_OWN_MARGIN [`cA:real`; `sA:real`; `cD:real`; `sD:real`] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  FAWPR_USE FAWPR_FACE [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
    `uA:real`; `&3 * cA - (&12 / &5) * sA - &1`] THEN
  FAWPR_USE ABT_CLOSED_BOUNDS [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
    `cA * uA - sA * (&3 * cA - (&12 / &5) * sA - &1)`;
    `sA * uA + cA * (&3 * cA - (&12 / &5) * sA - &1)`; `cD:real`; `sD:real`] THEN
  SUBGOAL_THEN
   `cD * (cA * uA - sA * (&3 * cA - (&12 / &5) * sA - &1)) +
    sD * (sA * uA + cA * (&3 * cA - (&12 / &5) * sA - &1)) - &2 * (cD + sD) =
    (cA * cD + sA * sD) * (uA - &2 * (cA + sA)) +
    (cA * sD - sA * cD) * (cA - &1 - (&2 / &5) * sA)` ASSUME_TAC THENL
  [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  FAWPR_PRODLT_TAC `cA * cD + sA * sD` `(&13 / &50) * sA - (uA - &2 * (cA + sA))` THEN
  SUBGOAL_THEN
   `(&2 / &5) * cD + sD + (cA * cD + sA * sD) * ((&13 / &50) * sA) +
    (cA * sD - sA * cD) * (cA - &1 - (&2 / &5) * sA) =
    cD * fawpm_f cA sA + sD * fawpm_g cA sA` ASSUME_TAC THENL
  [REWRITE_TAC[fawpm_f; fawpm_g] THEN
   UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  FAWPR_USE FAWPM_MARGIN [`cA:real`; `sA:real`; `cD:real`; `sD:real`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: bottom_face *)
let FAWPR_BOTTOM_FACE = prove
 (`forall c s u v a.
     c977cc_normal c s /\ linside c s u v a (&2) (&2) /\
     u < (&8 / &5) * c + s /\ ~linside c s u v a (&8 / &5) (&1)
     ==> c - (&8 / &5) * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPR_NORMAL_TAC THEN
  MP_TAC(ASSUME `linside c s u v a (&2) (&2)`) THEN
  MP_TAC(ASSUME `~linside c s u v a (&8 / &5) (&1)`) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: point *)
let FAWPR_POINT = prove
 (`forall c s u v a.
     c977cc_normal c s /\ &1 < a /\ linside c s u v a (&2) (&2) /\
     linside c s u v a (&2) (&3 / &2) /\
     u + a - &2 * (c + s) < &1 / &10 /\ c - (&8 / &5) * s <= v
     ==> linside c s u v a (&6 / &5) (&19 / &10)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPR_NORMAL_TAC THEN
  SUBGOAL_THEN `(&9 / &10) * c + (&2 / &5) * s <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `(&2 / &5) * c - (&9 / &10) * s`]; ALL_TAC] THEN
  MP_TAC(ASSUME `linside c s u v a (&2) (&2)`) THEN
  MP_TAC(ASSUME `linside c s u v a (&2) (&3 / &2)`) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;
