(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C896Completion.lean               *)
(* (namespace N12Compact.FiniteCases.C896Ending; Lean header: "This source   *)
(* has not been compiled").  Original C896 family and retained-row 483       *)
(* contracts.  rowAt 483 / retainedRows / ExcludesFamily / ExcludesCase:     *)
(* EL 483 ROWS / rows with MEM (EL j COVER_IDS) EXPECTED_IDS / excl_fam /    *)
(* excl_case (RowIdentity.ml).  The private lookup is ri_lookup 483;         *)
(* C896Ending.impossible is C896CE_IMPOSSIBLE.  Tag C896CO_.                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C896Centers.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: lookup (private) *)
let C896CO_LOOKUP = ri_lookup 483 `c896d_family`;;

(* Lean: row_family *)
let C896CO_ROW_FAMILY = ri_family_at 483 `c896d_family`;;

(* Lean: family_excluded *)
let C896CO_FAMILY_EXCLUDED = prove
 (`excl_fam c896d_family`,
  REWRITE_TAC[excl_fam] THEN MESON_TAC[C896CE_IMPOSSIBLE]);;

(* Lean: case_excluded *)
let C896CO_CASE_EXCLUDED = MP (ri_excludes_case 483 `c896d_family`) C896CO_FAMILY_EXCLUDED;;
