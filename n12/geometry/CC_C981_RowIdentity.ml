(* ========================================================================= *)
(* Phase 2: Completion/Cases/C981/RowIdentity.lean.                          *)
(* The C981 family is the retained row 512 (original id 981).                *)
(* ========================================================================= *)

needs "n12/geometry/RowIdentity.ml";;

(* Lean: family *)
let ccc981ri_family = new_definition
 `ccc981ri_family = {1, 2, 12, 48, 192, 512, 1024, 2048, 4096, 8192, 16384, 32768}`;;

(* Lean: lookup (private) *)
let CCC981RI_LOOKUP = ri_lookup 512 `ccc981ri_family`;;

(* Lean: row_family *)
let CCC981RI_ROW_FAMILY = ri_family_at 512 `ccc981ri_family`;;

(* Lean: family_retained *)
let CCC981RI_FAMILY_RETAINED = ri_family_retained 512 `ccc981ri_family`;;

(* Lean: excludes_case_iff *)
let CCC981RI_EXCLUDES_CASE_IFF = ri_excludes_case_iff 512 `ccc981ri_family`;;

(* the forward direction, as in the other RowIdentity ports *)
let CCC981RI_EXCLUDES_CASE = ri_excludes_case 512 `ccc981ri_family`;;
