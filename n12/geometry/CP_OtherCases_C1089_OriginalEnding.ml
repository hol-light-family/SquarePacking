(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/OriginalEnding.lean           *)
(* (namespace N12Compact.Completion.OtherCases.C1089.OriginalData).  The     *)
(* original C1089 family and retained row 573, joined through all closed     *)
(* wall-center sectors.  family = c1089sc_family; owners p 8 / 10 / 11 are   *)
(* the owners at masks 4096 / 16384 / 32768.  ExcludesFamily = excl_fam,     *)
(* ExcludesCase = excl_case; RowIdentity.family_at = ri_family_at.           *)
(* Sector theorems: AllPositive (C1089AP_), SectorEntrances (C1089SE_),      *)
(* LastActual (C1089LA_), SectorEndings (C1089SN_), ReverseStructural        *)
(* (C1089RS_), WallCore (C1089WC_).  le_of_not_ge is REAL_LE_TOTAL.          *)
(* (Lean header: "Source only".)  Tag C1089OE_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_AllPositive.ml";;
needs "n12/geometry/CP_OtherCases_C1089_SectorEndings.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ReverseStructural.ml";;
needs "n12/geometry/CP_OtherCases_C1089_LastActual.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: family_excluded *)
let C1089OE_FAMILY_EXCLUDED = prove
 (`excl_fam c1089sc_family`,
  REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  let split t = DISJ_CASES_TAC (SPECL [`&2`; t] REAL_LE_TOTAL) in
  let close th = MP_TAC (SPEC_ALL th) THEN ASM_REWRITE_TAC[] in
  split (c1089wc_lcy 4096) THENL
   [split (c1089wc_lcy 16384) THENL
     [split (c1089wc_lcx 32768) THENL
       [close C1089AP_IMPOSSIBLE; close C1089SE_MMMP_IMPOSSIBLE];
      split (c1089wc_lcx 32768) THENL
       [close C1089LA_IMPOSSIBLE; close C1089SN_OPPOSED_IMPOSSIBLE]];
    split (c1089wc_lcy 16384) THENL
     [split (c1089wc_lcx 32768) THENL
       [close C1089SN_NORTHEAST_INWARD_IMPOSSIBLE; close C1089RS_IMPOSSIBLE];
      close C1089WC_TWO_LOW_IMPOSSIBLE]]);;

(* Lean: lookup (private) *)
let C1089OE_LOOKUP = ri_lookup 573 `c1089sc_family`;;

(* Lean: row_family *)
let C1089OE_ROW_FAMILY = ri_family_at 573 `c1089sc_family`;;

(* Lean: case_excluded *)
let C1089OE_CASE_EXCLUDED = MP (ri_excludes_case 573 `c1089sc_family`) C1089OE_FAMILY_EXCLUDED;;

(* for the assembly: |- EXCLUDED_ROW 573 *)
let C1089OE_EXCLUDED_ROW = ri_excluded_row 573 C1089OE_CASE_EXCLUDED;;
