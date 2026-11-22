(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C715/RowIdentity.lean.             *)
(* The C715 family is the retained row 396 (original id 715).                *)
(* ========================================================================= *)

needs "n12/geometry/RowIdentity.ml";;

(* Lean: family, ownerCode *)
let c715ri_family = new_definition
 `c715ri_family = {1,2,12,16,32,192,512,2304,4096,8192,17408,32768}`;;
let c715ri_owner_code = new_definition
 `c715ri_owner_code = [1;2;12;16;32;192;512;2304;4096;8192;17408;32768]`;;

(* Lean: lookup (private) *)
let C715RI_LOOKUP = ri_lookup 396 `c715ri_family`;;

(* Lean: row_family *)
let C715RI_ROW_FAMILY = ri_family_at 396 `c715ri_family`;;

(* Lean: excludes_case *)
let C715RI_EXCLUDES_CASE = ri_excludes_case 396 `c715ri_family`;;
