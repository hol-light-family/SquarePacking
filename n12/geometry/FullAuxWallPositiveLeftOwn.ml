(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveLeftOwn.lean                   *)
(* (N12Compact.FullAuxWallPositiveLeftOwn).  Exact support inequalities for  *)
(* the remaining left-owned longitudinal separator.  Normal is               *)
(* c977cc_normal, lower is ABT_lower, InsideContainer is lcont,              *)
(* FourSquareBLBridge.left_wall is FSBL_LEFT_WALL, lower_pp is               *)
(* FAWTE_LOWER_PP.  The Lean lets alpha, H, u are written out                *)
(* (alpha = cL*cD+sL*sD, H = sL*cD-cL*sD).  Tag FAWPLO_.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FullAuxWallSmallPositiveLeftB.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let FAWPLO_LIN = NLIN_TAC ~deg2:false [];;

let FAWPLO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FAWPLO_LIN; ALL_TAC];;

let FAWPLO_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th)
    else NO_TAC));;

(* Lean: wall_support (private) *)
let FAWPLO_WALL_SUPPORT = prove
 (`forall cL sL uL vL aL.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ c977cc_normal cL sL /\ lcont cL sL uL vL aL /\
     linside cL sL uL vL aL (&457 / &500) (&2)
     ==> aL * cL + &2 * cL * sL - (&457 / &500) * sL pow 2 <= cL * (uL + aL)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  FAWPLO_NORMAL_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FAWPLO_LIN; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`; lcx] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  FAWPLO_PROD `&0 <= sL * ((vL + aL) - (--sL * (&457 / &500) + cL * &2))` THEN
  REWRITE_TAC[REAL_POW_2] THEN FAWPLO_LIN);;

(* Lean: above *)
let FAWPLO_ABOVE = prove
 (`forall cL sL uL vL aL cD sD uD vD aD.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     c977cc_normal cL sL /\ c977cc_normal cD sD /\ &1 < aD /\ aL = aD /\
     lcont cL sL uL vL aL /\ linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cD sD uD vD aD (&2) (&3 / &2) /\
     &0 <= sL * cD - cL * sD /\
     uL + aL <= ABT_lower cD sD uD vD aD cL sL
     ==> &0 < &2 - (&543 / &500) * sL pow 2 - cL * (&1 + (cL * cD + sL * sD)) -
              (&1 / &2) * cL * cD * (sL * cD - cL * sD) +
              cL * (cL * cD + sL * sD) * (uD + aD - &2 * (cD + sD))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FAWPLO_WALL_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aD`)) THEN
  FAWPLO_NORMAL_TAC THEN
  FAWPLO_PROD `&0 < cL * cD` THEN FAWPLO_PROD `&0 <= sL * sD` THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `cL:real`; `sL:real`]
    FAWTE_LOWER_PP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FAWPLO_LIN; DISCH_THEN SUBST_ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  FAWPLO_PROD `&0 <= cL * (((cL * cD + sL * sD) * uD + (--cL * sD + sL * cD) * vD) - (uL + aD))` THEN
  FAWPLO_PROD `&0 <= (cL * (sL * cD - cL * sD)) * ((--sD * &2 + cD * (&3 / &2)) - vD)` THEN
  FAWPLO_PROD `&0 < (aD - &1) * (cL * (&1 + (cL * cD + sL * sD)))` THEN
  SUBGOAL_THEN `(&2 * cL * cL + &2 * cL * sL) * (cD * cD + sD * sD) = &2 * cL * cL + &2 * cL * sL`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN FAWPLO_LIN);;

(* ABT_lower when the first band coefficient is >= 0 and the second <= 0 *)
let FAWPLO_LOWER_PN = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ --x * s + y * c <= &0
     ==> ABT_lower c s u v a x y = (x * c + y * s) * u + (--x * s + y * c) * (v + a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REAL_ARITH_TAC);;

(* Lean: below *)
let FAWPLO_BELOW = prove
 (`forall cL sL uL vL aL cD sD uD vD aD.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     c977cc_normal cL sL /\ c977cc_normal cD sD /\ &1 < aD /\ aL = aD /\
     lcont cL sL uL vL aL /\ linside cL sL uL vL aL (&457 / &500) (&2) /\
     cD - (&8 / &5) * sD <= vD /\
     sL * cD - cL * sD <= &0 /\
     uL + aL <= ABT_lower cD sD uD vD aD cL sL
     ==> &0 < &2 - (&543 / &500) * sL pow 2 - cL * (&1 + (cL * cD + sL * sD)) +
              cL * (sL * cD - cL * sD) * (&1 - cD + (&2 / &5) * sD) +
              cL * (cL * cD + sL * sD) * (uD + aD - &2 * (cD + sD))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FAWPLO_WALL_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aD`)) THEN
  FAWPLO_NORMAL_TAC THEN
  FAWPLO_PROD `&0 < cL * cD` THEN FAWPLO_PROD `&0 <= sL * sD` THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `cL:real`; `sL:real`]
    FAWPLO_LOWER_PN) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FAWPLO_LIN; DISCH_THEN SUBST_ALL_TAC] THEN
  FAWPLO_PROD `&0 <= cL * (((cL * cD + sL * sD) * uD + (--cL * sD + sL * cD) * (vD + aD)) - (uL + aD))` THEN
  FAWPLO_PROD `&0 <= (cL * --(sL * cD - cL * sD)) * (vD - (cD - (&8 / &5) * sD))` THEN
  FAWPLO_PROD `&0 < (aD - &1) * (cL * (&1 + (cL * cD + sL * sD) - (sL * cD - cL * sD)))` THEN
  SUBGOAL_THEN `(&2 * cL * cL + &2 * cL * sL) * (cD * cD + sD * sD) = &2 * cL * cL + &2 * cL * sL`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN FAWPLO_LIN);;
