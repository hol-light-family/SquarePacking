(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C974/Completion.lean                *)
(* (N12Compact.Completion.OtherCases.C974.OriginalData).  C974 original-     *)
(* family and retained-row 505 contracts.  family is c974d_family;           *)
(* ActualEnding.impossible C974AE_IMPOSSIBLE; ExcludesFamily / ExcludesCase  *)
(* excl_fam / excl_case; rowAt 505 via ri_lookup / ri_family_at.             *)
(* (Lean header: "source proofs awaiting compilation".)  Tag C974CO_.        *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C974_ActualEnding.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: lookup (private) *)
let C974CO_LOOKUP = ri_lookup 505 `c974d_family`;;

(* Lean: row_family *)
let C974CO_ROW_FAMILY = ri_family_at 505 `c974d_family`;;

(* Lean: family_excluded *)
let C974CO_FAMILY_EXCLUDED = prove
 (`excl_fam c974d_family`,
  REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C974AE_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* Lean: case_excluded *)
let C974CO_CASE_EXCLUDED = MP (ri_excludes_case 505 `c974d_family`) C974CO_FAMILY_EXCLUDED;;

let C974CO_EXCLUDED_ROW = ri_excluded_row 505 C974CO_CASE_EXCLUDED;;
