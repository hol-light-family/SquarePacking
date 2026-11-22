(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C975Completion.lean                *)
(* (namespace N12Compact.FiniteCases.C975Selection).  C975 original-family   *)
(* and retained-row 506 contracts.  family is c975d_family; C975Ending's     *)
(* impossible is C975EN_IMPOSSIBLE; ExcludesFamily / ExcludesCase are        *)
(* excl_fam / excl_case; rowAt 506 via ri_lookup / ri_family_at.             *)
(* (Lean header: complete source proof, no kernel acceptance asserted.)      *)
(* Tag C975CO_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975Ending.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: lookup (private) *)
let C975CO_LOOKUP = ri_lookup 506 `c975d_family`;;

(* Lean: row_family *)
let C975CO_ROW_FAMILY = ri_family_at 506 `c975d_family`;;

(* Lean: family_excluded *)
let C975CO_FAMILY_EXCLUDED = prove
 (`excl_fam c975d_family`,
  REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C975EN_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* Lean: case_excluded *)
let C975CO_CASE_EXCLUDED = MP (ri_excludes_case 506 `c975d_family`) C975CO_FAMILY_EXCLUDED;;

(* for the assembly: |- EXCLUDED_ROW 506 *)
let C975CO_EXCLUDED_ROW = ri_excluded_row 506 C975CO_CASE_EXCLUDED;;
