(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976/Completion.lean                *)
(* (namespace N12Compact.Completion.OtherCases.C976.OriginalData).          *)
(* Original C976 family and the retained-row 507 adapter.  rowAt 507 is     *)
(* EL 507 ROWS (RowIdentity.ml); ExcludesFamily / ExcludesCase are          *)
(* excl_fam / excl_case.  Tag C976CO_.                                      *)
(* (Lean header: "source proofs awaiting compilation".)                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C976_ActualEnding.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: lookup (private) *)
let C976CO_LOOKUP = ri_lookup 507 `c976od_family`;;

(* Lean: row_family *)
let C976CO_ROW_FAMILY = ri_family_at 507 `c976od_family`;;

(* Lean: family_excluded *)
let C976CO_FAMILY_EXCLUDED = prove
 (`excl_fam c976od_family`,
  REWRITE_TAC[excl_fam] THEN MESON_TAC[C976AE_IMPOSSIBLE]);;

(* Lean: case_excluded *)
let C976CO_CASE_EXCLUDED = MP (ri_excludes_case 507 `c976od_family`) C976CO_FAMILY_EXCLUDED;;

(* whole-case closer: retained row 507 (case 976) *)
let C976CO_EXCLUDED_ROW = ri_excluded_row 507 C976CO_CASE_EXCLUDED;;
