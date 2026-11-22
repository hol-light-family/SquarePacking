(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C705716/RowIdentity.lean.          *)
(* Lean indexes by b : Bool (false = C705, retained row 386; true = C716,     *)
(* retained row 397).  HOL: one constant per index (suffix _f / _t) and the   *)
(* theorems for both indices (OCaml pairs (b = false, b = true)).            *)
(* ========================================================================= *)

needs "n12/geometry/RowIdentity.ml";;

(* Lean: family *)
let c705716ri_family_f = new_definition
 `c705716ri_family_f = {1,2,12,16,32,192,256,3584,4096,8192,16384,32768}`;;
let c705716ri_family_t = new_definition
 `c705716ri_family_t = {1,2,12,16,32,192,512,3328,4096,8192,16384,32768}`;;

(* Lean: caseId *)
let c705716ri_case_id = new_definition
 `c705716ri_case_id (b:bool) = if b then 716 else 705`;;

(* Lean: ownerCode *)
let c705716ri_owner_code = new_definition
 `c705716ri_owner_code (b:bool) =
    [1;2;12;16;32;192;(if b then 512 else 256);(if b then 3328 else 3584);4096;8192;16384;32768]`;;

(* Lean: lookup (private) *)
let C705716RI_LOOKUP =
  (ri_lookup 386 `c705716ri_family_f`, ri_lookup 397 `c705716ri_family_t`);;

(* Lean: row_family *)
let C705716RI_ROW_FAMILY =
  (ri_family_at 386 `c705716ri_family_f`, ri_family_at 397 `c705716ri_family_t`);;

(* Lean: excludes_case *)
let C705716RI_EXCLUDES_CASE =
  (ri_excludes_case 386 `c705716ri_family_f`, ri_excludes_case 397 `c705716ri_family_t`);;

(* the case ids of the two theorems agree with caseId false / caseId true *)
let C705716RI_CASE_ID = prove
 (`c705716ri_case_id false = 705 /\ c705716ri_case_id true = 716`,
  REWRITE_TAC[c705716ri_case_id]);;
