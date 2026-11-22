(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointComplete.lean *)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointGeometry; Lean header:      *)
(* "Source only, uncompiled").  The missing-negative transfer with the four  *)
(* complete continuous scalar bounds.  ScalarProof is c1092mncac_scalarProof *)
(* (ModesNonnegative c1092mncge_modesNonnegative); G00star_lower ..          *)
(* G11star_lower are C1092MMNCC_G00STAR_LOWER, C1092MNG01_G01STAR_LOWER,     *)
(* C1092MMNG10_G10STAR_LOWER, C1092MNCG11_G11STAR_LOWER; crosspoint is       *)
(* C1092MNCAC_CROSSPOINT_OF_SCALARS with the scalar proof discharged (same   *)
(* hypotheses, conventions of CP_C1092_MPPMMissingNegativeCrosspointActual.ml).*)
(* Tag C1092MNCCO_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointActual.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointCentral.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointG01.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointG10.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointG11.ml";;

(* Lean: scalar_proof *)
let C1092MNCCO_SCALAR_PROOF = prove
 (`c1092mncac_scalarProof`,
  REWRITE_TAC[c1092mncac_scalarProof; c1092mncge_modesNonnegative] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `&1 / &250` THEN CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC C1092MMNCC_G00STAR_LOWER];
    EXISTS_TAC `&1 / &100` THEN CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC C1092MNG01_G01STAR_LOWER];
    EXISTS_TAC `&1 / &250` THEN CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC C1092MMNG10_G10STAR_LOWER];
    EXISTS_TAC `&1 / &100` THEN CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC C1092MNCG11_G11STAR_LOWER]] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* Lean: crosspoint *)
let C1092MNCCO_CROSSPOINT =
  REWRITE_RULE[C1092MNCCO_SCALAR_PROOF] C1092MNCAC_CROSSPOINT_OF_SCALARS;;
