(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveLowerAngleSupport.lean        *)
(* (Jatloe, N12-jatloe; namespace                                            *)
(* N12Compact.FullAuxWallPositiveLowerAngleSupport).  Both transverse C/B    *)
(* separators imply a scalar obstruction near the axis.  Normal is           *)
(* c977cc_normal; lower_pp: FAWTE_LOWER_PP; the upper band formula with a    *)
(* nonpositive first coefficient is FAWPTP_UPPER_NP;                         *)
(* FullAuxWallPositiveLowerAngle.c_axis / b_axis: FAWPLA_C_AXIS /            *)
(* FAWPLA_B_AXIS.  The OpenSquare invariants are explicit hypotheses.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FullAuxWallPositiveTop.ml";;
needs "n12/geometry/FullAuxWallPositiveLowerAngle.ml";;

let FAWPLAS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPLAS_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let FAWPLAS_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: cuts *)
let FAWPLAS_CUTS = prove
 (`forall cD sD uD vD aD cB sB uB vB aB.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cD sD /\ c977cc_normal cB sB /\ &1 < aD /\ aD = aB /\
     cD - (&8 / &5) * sD <= vD /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     sD * cB <= cD * sB /\
     (vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB)
     ==> &1 < cD * (&2 - cB - sB + (&3 / &5) * cB * sB) +
              sD * (cB - sB + (&3 / &5) * sB pow 2) \/
         &1 + cB * (cD - sD + sD pow 2 + (&2 / &5) * cD * sD - &2) +
         sB * (cD + sD + (&2 / &5) * sD pow 2 - cD * sD - &1) -
         (cD * sB - sD * cB) * (uD + aD - &2 * (cD + sD)) < &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aD:real = aB`)) THEN
  FAWPLAS_NORMAL_TAC THEN
  FAWPLAS_PRODLT_TAC `cD:real` `cB:real` THEN FAWPLAS_PROD_TAC `sD:real` `sB:real` THEN
  FAWPLAS_PRODLT_TAC `aD - &1` `&1 + (cD * cB + sD * sB) + (cD * sB - sD * cB)` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [DISJ1_TAC THEN
   MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aD:real`; `--sD`; `cD:real`]
     FAWTE_LOWER_PP) THEN
   ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
   SUBGOAL_THEN `ABT_lower cB sB uB vB aD (--sD) cD =
                 (cD * sB - sD * cB) * uB + (cD * cB + sD * sB) * vB` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   FAWPLAS_PROD_TAC `cD * sB - sD * cB` `(&8 / &5) * cB + &3 * sB - (uB + aD)` THEN
   FAWPLAS_PROD_TAC `cD * cB + sD * sB` `&3 * cB - sB - (vB + aD)` THEN
   SUBGOAL_THEN
    `(cD * sB - sD * cB) * ((&8 / &5) * cB + &3 * sB) + (cD * cB + sD * sB) * (&3 * cB - sB) -
     (cD - (&8 / &5) * sD) - (&1 + (cD * cB + sD * sB) + (cD * sB - sD * cB)) =
     cD * (&2 - cB - sB + (&3 / &5) * cB * sB) +
     sD * (cB - sB + (&3 / &5) * sB pow 2) - &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   NLIN_TAC ~deg2:false [];
   DISJ2_TAC THEN
   MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `--sB`; `cB:real`]
     FAWPTP_UPPER_NP) THEN
   ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
   SUBGOAL_THEN `ABT_upper cD sD uD vD aD (--sB) cB =
                 --(cD * sB - sD * cB) * uD + (cD * cB + sD * sB) * (vD + aD)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   FAWPLAS_PROD_TAC `cD * cB + sD * sB` `vD - (cD - (&8 / &5) * sD)` THEN
   SUBGOAL_THEN
    `(&1 + (cD * cB + sD * sB) + (cD * sB - sD * cB)) -
     (cD * sB - sD * cB) * (&2 * (cD + sD) + (uD + aD - &2 * (cD + sD))) +
     (cD * cB + sD * sB) * (cD - (&8 / &5) * sD) - (&3 * cB - sB) =
     &1 + cB * (cD - sD + sD pow 2 + (&2 / &5) * cD * sD - &2) +
     sB * (cD + sD + (&2 / &5) * sD pow 2 - cD * sD - &1) -
     (cD * sB - sD * cB) * (uD + aD - &2 * (cD + sD))` ASSUME_TAC THENL
   [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   NLIN_TAC ~deg2:false []]);;

(* Lean: sine *)
let FAWPLAS_SINE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cD sD /\ c977cc_normal cB sB /\ &1 < aD /\ aD = aB /\
     cD - (&8 / &5) * sD <= vD /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     &3 / &10 < sB /\ uD + aD - &2 * (cD + sD) <= &1 / &112 /\
     sD * cB <= cD * sB /\
     (vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB)
     ==> &1 / &20 < sD`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FAWPLAS_CUTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `sB:real`] FAWPLA_C_AXIS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `sB:real`; `uD + aD - &2 * (cD + sD)`]
    FAWPLA_B_AXIS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RASM_ARITH_TAC);;
