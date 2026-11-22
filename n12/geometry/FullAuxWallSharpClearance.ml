(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallSharpClearance.lean (Jatloe,          *)
(* N12-jatloe; namespace N12Compact.FullAuxWallSharpClearance).              *)
(* Retaining the exact right-wall clearance gives uniform bounds; both       *)
(* actual A/C longitudinal support selectors are retained.  Normal is        *)
(* c977cc_normal; upper/lower are ABT_upper/ABT_lower; lower_pp is           *)
(* FAWTE_LOWER_PP; FullAuxWallRightMargin.central_bounds is                  *)
(* FAWRM_CENTRAL_BOUNDS.  The Lean local abbreviations (e, u, v, alpha,      *)
(* gamma, K) are written out.  The OpenSquare invariants are explicit        *)
(* hypotheses.                                                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallRightMargin.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;

let FAWSC_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWSC_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let FAWSC_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let FAWSC_RING_TAC =
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
    filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
  CONV_TAC REAL_RING;;

(* Lean: excess *)
let FAWSC_EXCESS = prove
 (`forall c s e. c977cc_normal c s /\ &4 * s <= c /\
           c * e + (&2 / &5) * s pow 2 - (&1 - c) * (&1 - s) < &0
           ==> e < &1 / &1250`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] FAWRM_CENTRAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FAWSC_NORMAL_TAC THEN
  FAWSC_PROD_TAC `(&25 / &49) * s pow 2 - (&1 - c)` `&1 - s` THEN
  FAWSC_PROD_TAC `(s - &18 / &125) pow 2` `&125 * s + &9` THEN
  SUBGOAL_THEN `&2916 / &15625 - s pow 2 * (&27 - &125 * s) =
                (s - &18 / &125) pow 2 * (&125 * s + &9)` ASSUME_TAC THENL
  [CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&245 * c * e < &2916 / &15625`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FAWSC_PROD_TAC `c:real` `e - &1 / &1250` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: angle *)
let FAWSC_ANGLE = prove
 (`forall c s e. c977cc_normal c s /\ &4 * s <= c /\ &0 <= e /\
           c * e + (&2 / &5) * s pow 2 - (&1 - c) * (&1 - s) < &0
           ==> &977 / &1000 <= c /\ s < &21 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWSC_NORMAL_TAC THEN
  FAWSC_PROD_TAC `c - &4 * s` `c + &4 * s` THEN
  SUBGOAL_THEN `&97 / &100 <= c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FAWSC_PRODLT_TAC `&97 / &100 - c` `&97 / &100 + c` THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  FAWSC_PROD_TAC `c:real` `e:real` THEN
  SUBGOAL_THEN `(&2 / &5) * s pow 2 - (&1 - c) * (&1 - s) =
                (&1 - c) * (s + (&2 / &5) * c - &3 / &5)` ASSUME_TAC THENL
  [FAWSC_RING_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s + (&2 / &5) * c < &3 / &5` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FAWSC_PROD_TAC `&1 - c` `s + (&2 / &5) * c - &3 / &5` THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `s < &53 / &250` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FAWSC_PRODLT_TAC `&53 / &250 - s` `&53 / &250 + s` THEN
  SUBGOAL_THEN `&977 / &1000 <= c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FAWSC_PRODLT_TAC `&977 / &1000 - c` `&977 / &1000 + c` THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: angular_margin (private) *)
let FAWSC_ANGULAR_MARGIN = prove
 (`forall c s. c977cc_normal c s /\ &977 / &1000 <= c /\ s <= &21 / &100
         ==> &50 * c * (&1 - c) <= &11 * ((&1 - c) * (&1 - s) + (&2 / &5) * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWSC_NORMAL_TAC THEN
  FAWSC_PROD_TAC `s:real` `&1 - c` THEN
  FAWSC_PROD_TAC `&21 / &100 - s` `&39 + &11 * (s + &21 / &100)` THEN
  SUBGOAL_THEN `&0 <= &11 * s * (&1 - s) + (&22 / &5) * (&1 + c) - &50 * c * s`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSC_PROD_TAC `s:real` `&11 * s * (&1 - s) + (&22 / &5) * (&1 + c) - &50 * c * s` THEN
  SUBGOAL_THEN
   `(&1 + c) * (&11 * ((&1 - c) * (&1 - s) + (&2 / &5) * s) - &50 * c * (&1 - c)) =
    s * (&11 * s * (&1 - s) + (&22 / &5) * (&1 + c) - &50 * c * s)` ASSUME_TAC THENL
  [FAWSC_RING_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FAWSC_PRODLT_TAC `&1 + c`
    `&50 * c * (&1 - c) - &11 * ((&1 - c) * (&1 - s) + (&2 / &5) * s)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: upper_pn (private) *)
let FAWSC_UPPER_PN = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ --x * s + y * c <= &0
     ==> ABT_upper c s u v a x y = (x * c + y * s) * (u + a) + (--x * s + y * c) * v`,
  REPEAT STRIP_TAC THEN C981NP_FORM_TAC);;

(* Lean: opposite_slope *)
let FAWSC_OPPOSITE_SLOPE = prove
 (`forall cA sA uA vA aA cD sD uD vD aD.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     c977cc_normal cA sA /\ c977cc_normal cD sD /\ &1 < aA /\ &4 * sA <= cA /\
     &2 * (cA + sA) <= uA /\
     cA * (uA - &2 * (cA + sA)) + (&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA) < &0 /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&2) (&2) /\ linside cD sD uD vD aD (&2) (&3 / &2) /\
     (ABT_upper cD sD uD vD aD cA sA <= uA \/ uD + aD <= ABT_lower cA sA uA vA aA cD sD)
     ==> &50 * sD < &11 * cD`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA - &2 * (cA + sA)`] FAWSC_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA - &2 * (cA + sA)`] FAWSC_EXCESS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ASSUME `linside cD sD uD vD aD (&2) (&2)`) THEN
  MP_TAC(ASSUME `linside cD sD uD vD aD (&2) (&3 / &2)`) THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  FAWSC_NORMAL_TAC THEN
  FAWSC_PRODLT_TAC `cA:real` `cD:real` THEN FAWSC_PROD_TAC `sA:real` `sD:real` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FAWSC_PROD_TAC `cA:real` `&50 * sD - &11 * cD` THEN
  FAWSC_PROD_TAC `cD:real` `(&11 / &50) * cA - sA - &1 / &250` THEN
  SUBGOAL_THEN `cD / &250 <= cA * sD - sA * cD` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `cA:real`; `sA:real`]
     FAWSC_UPPER_PN) THEN
   ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
   SUBGOAL_THEN
    `ABT_upper cD sD uD vD aD cA sA - &2 * (cA + sA) =
     (cA * cD + sA * sD) * (uD + aD - &2 * (cD + sD)) +
     (cA * sD - sA * cD) * (&2 * (cD - sD) - vD)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FAWSC_RING_TAC; ALL_TAC] THEN
   FAWSC_PRODLT_TAC `cA * sD - sA * cD` `(&2 * (cD - sD) - vD) - cD / &2` THEN
   FAWSC_PRODLT_TAC `cA * cD + sA * sD` `uD + aD - &2 * (cD + sD)` THEN
   FAWSC_PROD_TAC `cD:real` `(cA * sD - sA * cD) - cD / &250` THEN
   FAWSC_PROD_TAC `cD - &7 / &10` `cD + &7 / &10` THEN
   NLIN_TAC ~deg2:false [];
   MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `cD:real`; `sD:real`]
     FAWTE_LOWER_PP) THEN
   ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
   SUBGOAL_THEN
    `ABT_lower cA sA uA vA aA cD sD - &2 * (cD + sD) =
     (cA * cD + sA * sD) * (uA - &2 * (cA + sA)) +
     (cA * sD - sA * cD) * (vA - &2 * (cA - sA))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FAWSC_RING_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `vA - &2 * (cA - sA) < cA - &1 - (&2 / &5) * sA` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < (cA * cD + sA * sD) * (uA - &2 * (cA + sA)) +
                      (cA * sD - sA * cD) * (vA - &2 * (cA - sA))` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   FAWSC_PRODLT_TAC `cA:real` `(cA * cD + sA * sD) * (uA - &2 * (cA + sA)) +
                      (cA * sD - sA * cD) * (vA - &2 * (cA - sA))` THEN
   FAWSC_PRODLT_TAC `cA * cD + sA * sD`
     `(&1 - cA) * (&1 - sA) - (&2 / &5) * sA pow 2 - cA * (uA - &2 * (cA + sA))` THEN
   SUBGOAL_THEN `&0 < cA * (cA * sD - sA * cD)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
   FAWSC_PRODLT_TAC `cA * (cA * sD - sA * cD)`
     `(cA - &1 - (&2 / &5) * sA) - (vA - &2 * (cA - sA))` THEN
   SUBGOAL_THEN
    `(cA * cD + sA * sD) * ((&1 - cA) * (&1 - sA) - (&2 / &5) * sA pow 2) +
     cA * (cA * sD - sA * cD) * (cA - &1 - (&2 / &5) * sA) =
     cD * cA * (&1 - cA) - sD * ((&1 - cA) * (&1 - sA) + (&2 / &5) * sA)` ASSUME_TAC THENL
   [FAWSC_RING_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`cA:real`; `sA:real`] FAWSC_ANGULAR_MARGIN) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN `&0 <= (&1 - cA) * (&1 - sA) + (&2 / &5) * sA` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
   FAWSC_PROD_TAC `cD:real`
     `&11 * ((&1 - cA) * (&1 - sA) + (&2 / &5) * sA) - &50 * cA * (&1 - cA)` THEN
   FAWSC_PROD_TAC `(&1 - cA) * (&1 - sA) + (&2 / &5) * sA` `&50 * sD - &11 * cD` THEN
   NLIN_TAC ~deg2:false []]);;
