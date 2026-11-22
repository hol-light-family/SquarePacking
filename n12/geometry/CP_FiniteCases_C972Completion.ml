(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972Completion.lean                *)
(* (namespace N12Compact.FiniteCases.C972).  Original C972 family and the    *)
(* retained-row 503 contracts.  family = c972d_family; RowIdentity rowAt /   *)
(* family_at / ExcludesFamily / ExcludesCase = ri_lookup / ri_family_at /    *)
(* excl_fam / excl_case (geometry/RowIdentity.ml).  Tag FC972C_.                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972NortheastPositiveEnding.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: lookup (private) *)
let FC972C_LOOKUP = ri_lookup 503 `c972d_family`;;

(* Lean: row_family *)
let FC972C_ROW_FAMILY = ri_family_at 503 `c972d_family`;;

(* Lean: family_excluded *)
let FC972C_FAMILY_EXCLUDED = prove
 (`excl_fam c972d_family`,
  PURE_REWRITE_TAC[excl_fam] THEN ACCEPT_TAC C972NPE_FAMILY_IMPOSSIBLE);;

(* Lean: case_excluded *)
let FC972C_CASE_EXCLUDED = MP (ri_excludes_case 503 `c972d_family`) FC972C_FAMILY_EXCLUDED;;

(* the assembly form (retained row 503 has id 972) *)
let FC972C_EXCLUDED_ROW = ri_excluded_row 503 FC972C_CASE_EXCLUDED;;
