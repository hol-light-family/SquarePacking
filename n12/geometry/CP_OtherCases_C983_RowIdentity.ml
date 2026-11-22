(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/RowIdentity.lean.             *)
(* The C983 family is the retained row 514 (original id 983).                *)
(* ========================================================================= *)

needs "n12/geometry/RowIdentity.ml";;

(* Lean: family, ownerCode *)
let c983ri_family = new_definition
 `c983ri_family = {1,2,12,48,192,512,1024,2304,4096,8192,16384,32768}`;;
let c983ri_owner_code = new_definition
 `c983ri_owner_code = [1;2;12;48;192;512;1024;2304;4096;8192;16384;32768]`;;

(* Lean: lookup (private) *)
let C983RI_LOOKUP = ri_lookup 514 `c983ri_family`;;

(* Lean: row_family *)
let C983RI_ROW_FAMILY = ri_family_at 514 `c983ri_family`;;

(* Lean: excludes_case *)
let C983RI_EXCLUDES_CASE = ri_excludes_case 514 `c983ri_family`;;
