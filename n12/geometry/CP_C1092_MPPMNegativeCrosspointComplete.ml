(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointComplete.lean      *)
(* (N12Compact.C1092MPPMNegativeCrosspointGeometry; Lean header: "Source     *)
(* only, uncompiled").  The retaining-negative crosspoint transfer with all  *)
(* four scalar modes supplied.  ScalarProof is c1092nca_scalarProof;         *)
(* crosspoint is C1092NCA_CROSSPOINT_OF_SCALARS with the scalar proof        *)
(* discharged (same hypotheses: CP_C1092_MPPMNegativeCrosspointActual.ml).   *)
(* Tag C1092NCC_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointActual.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointCentral.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointG01.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointG10High.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointG11.ml";;

(* Lean: scalar_proof *)
let C1092NCC_SCALAR_PROOF = prove
 (`c1092nca_scalarProof`,
  REWRITE_TAC[c1092nca_scalarProof; c1092ncg_modesNonnegative] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY DISCH_TAC THENL
   [MATCH_MP_TAC C1092MNCC_G00_NONNEGATIVE;
    MATCH_MP_TAC C1092NG01_G01_NONNEGATIVE;
    MATCH_MP_TAC C1092NG10H_G10_NONNEGATIVE;
    MATCH_MP_TAC C1092NG11_G11_NONNEGATIVE] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: crosspoint *)
let C1092NCC_CROSSPOINT =
  REWRITE_RULE[C1092NCC_SCALAR_PROOF] C1092NCA_CROSSPOINT_OF_SCALARS;;
