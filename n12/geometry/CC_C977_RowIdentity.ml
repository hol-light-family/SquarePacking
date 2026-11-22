(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/RowIdentity.lean.                          *)
(* The C977 family is the retained row 508 (original id 977).                *)
(* ========================================================================= *)

needs "n12/geometry/RowIdentity.ml";;

(* Lean: family *)
let ccc977ri_family = new_definition
 `ccc977ri_family = {1, 2, 12, 48, 192, 256, 512, 2048, 4096, 8192, 16384, 32768}`;;

(* Lean: lookup (private) *)
let CCC977RI_LOOKUP = ri_lookup 508 `ccc977ri_family`;;

(* Lean: row_family *)
let CCC977RI_ROW_FAMILY = ri_family_at 508 `ccc977ri_family`;;

(* Lean: family_retained *)
let CCC977RI_FAMILY_RETAINED = ri_family_retained 508 `ccc977ri_family`;;

(* Lean: excludes_case_iff *)
let CCC977RI_EXCLUDES_CASE_IFF = ri_excludes_case_iff 508 `ccc977ri_family`;;

(* the forward direction, as in the other RowIdentity ports *)
let CCC977RI_EXCLUDES_CASE = ri_excludes_case 508 `ccc977ri_family`;;
