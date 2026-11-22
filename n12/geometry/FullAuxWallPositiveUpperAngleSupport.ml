(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveUpperAngleSupport.lean        *)
(* (Jatloe, N12-jatloe; namespace                                            *)
(* N12Compact.FullAuxWallPositiveUpperAngleSupport).  Both actual C/B        *)
(* support selectors bound B's positive sine strictly below 23/50.           *)
(* Normal is c977cc_normal; upper/lower are ABT_upper/ABT_lower;             *)
(* FullAuxWallPositiveLowerAngleSupport.cuts is FAWPLAS_CUTS;                *)
(* FullAuxWallPositiveUpperAngle.c_axis / b_axis: FAWPUA_C_AXIS /            *)
(* FAWPUA_B_AXIS.  The OpenSquare invariants are explicit hypotheses.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallPositiveLowerAngleSupport.ml";;
needs "n12/geometry/FullAuxWallPositiveUpperAngle.ml";;

(* Lean: sine *)
let FAWPUAS_SINE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cD sD /\ c977cc_normal cB sB /\ &1 < aD /\ aD = aB /\
     cD - (&8 / &5) * sD <= vD /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     sD <= &11 / &50 /\ uD + aD - &2 * (cD + sD) <= &1 / &1000 /\
     sD * cB <= cD * sB /\
     (vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB)
     ==> sB < &23 / &50`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FAWPLAS_CUTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `sB:real`] FAWPUA_C_AXIS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `sB:real`; `uD + aD - &2 * (cD + sD)`]
    FAWPUA_B_AXIS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RASM_ARITH_TAC);;
