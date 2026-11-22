(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveLeft.lean                      *)
(* (N12Compact.FullAuxWallPositiveLeft).  Complete positive-L sector of the   *)
(* genuine C/B/L support cycle.  Normal is c977cc_normal, upper/lower are     *)
(* ABT_upper/ABT_lower, InsideContainer is lcont; the OpenSquare invariants   *)
(* (unit normal, positive side) of L, D, B are explicit hypotheses.           *)
(* Used: FAWPUAS_SINE, FAWSPLB_SINE, FAWLR_POSITIVE_LEFT_AXES,                *)
(* FAWPLO_ABOVE/BELOW, FAWPLAM_MARGIN, FAWPLBM_MARGIN, FAWPLN_IMPOSSIBLE.     *)
(* Tag FAWPL_.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallPositiveLeftOwn.ml";;
needs "n12/geometry/FullAuxWallPositiveLeftNeighbor.ml";;
needs "n12/geometry/FullAuxWallPositiveLeftAboveMargin.ml";;
needs "n12/geometry/FullAuxWallPositiveLeftBelowMargin.ml";;
needs "n12/geometry/FullAuxWallPositiveUpperAngleSupport.ml";;
needs "n12/geometry/FullAuxWallSmallPositiveLeftB.ml";;
needs "n12/geometry/FullAuxWallLeftResidual.ml";;

let FAWPL_QL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`];;
let FAWPL_QD = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`];;
let FAWPL_QB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

(* Lean: impossible *)
let FAWPL_IMPOSSIBLE = prove
 (`forall cL sL uL vL aL cD sD uD vD aD cB sB uB vB aB.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cL sL /\ c977cc_normal cD sD /\ c977cc_normal cB sB /\
     &1 < aD /\ aL = aD /\ aD = aB /\
     lcont cL sL uL vL aL /\
     sD <= &11 / &50 /\ &1 / &20 < sD /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\ linside cL sL uL vL aL (&1) (&8 / &5) /\
     linside cD sD uD vD aD (&2) (&2) /\ linside cD sD uD vD aD (&2) (&3 / &2) /\
     linside cD sD uD vD aD (&6 / &5) (&19 / &10) /\
     cD - (&8 / &5) * sD <= vD /\
     uD + aD - &2 * (cD + sD) <= &1 / &1000 /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\
     vB + aB <= &3 * cB - sB /\
     (&457 / &500) * cB + &2 * sB <= uB /\
     &3 / &10 < sB /\ sD * cB <= cD * sB /\
     (vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB) /\
     ldisj cL sL uL vL aL cD sD uD vD aD /\
     ldisj cL sL uL vL aL cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&1 < aB /\ aL = aB` STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (FAWPL_QD @ FAWPL_QB) FAWPUAS_SINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&1 < (&343 / &500) * cB + sB` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (FAWPL_QL @ FAWPL_QB) FAWSPLB_SINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL (FAWPL_QL @ FAWPL_QD) FAWLR_POSITIVE_LEFT_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_TAC) THENL
  [SUBGOAL_THEN `&0 <= uD + aD - &2 * (cD + sD)` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cD sD uD vD aD (&2) (&2)` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `&0 <= sL * cD - cL * sD` THENL
   [MP_TAC(SPECL (FAWPL_QL @ FAWPL_QD) FAWPLO_ABOVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`cL:real`; `sL:real`; `cD:real`; `sD:real`;
                  `uD + aD - &2 * (cD + sD)`] FAWPLAM_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `sL * cD - cL * sD <= &0` ASSUME_TAC THENL
    [RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL (FAWPL_QL @ FAWPL_QD) FAWPLO_BELOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`cL:real`; `sL:real`; `cD:real`; `sD:real`;
                  `uD + aD - &2 * (cD + sD)`] FAWPLBM_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    RASM_ARITH_TAC];
   MP_TAC(ISPECL (FAWPL_QL @ FAWPL_QD) FAWPLN_IMPOSSIBLE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; REWRITE_TAC[]]]);;
