(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/Completion.lean               *)
(* (namespace N12Compact.Completion.OtherCases.C1091.Completion).            *)
(* Unconditional assembly of case 1091: split on centerY (owners p 10) <= 2  *)
(* (owner 16384) and centerX (owners p 11) <= 2 (owner 32768); the four      *)
(* sectors are closed by EntranceWalls.right_low_top_low_impossible,         *)
(* EntranceNorthwest.impossible, EntranceMixed.impossible and                *)
(* EntranceAllPositive.impossible (with EntranceWalls.left_above).           *)
(* (Lean header: "Source only, uncompiled".)  Tag C1091CO_.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1091_EntranceMixed.ml";;
needs "n12/geometry/CP_OtherCases_C1091_EntranceNorthwest.ml";;
needs "n12/geometry/CP_OtherCases_C1091_RowIdentity.ml";;

(* Lean: family_excluded *)
let C1091CO_FAMILY_EXCLUDED = prove
 (`excl_fam c1091od_family`,
  REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  let hh = CONJ (ASSUME C1091EW_NP) (ASSUME C1091EW_IMG) in
  let close th = MP_TAC (SPEC_ALL th) THEN ASM_REWRITE_TAC[] in
  let split t = ASM_CASES_TAC (c1091ew_le t `&2`) THENL
    [ALL_TAC; FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o
                             REWRITE_RULE[REAL_NOT_LE])] in
  ASSUME_TAC (MATCH_MP REAL_LT_IMP_LE (MP (SPEC_ALL C1091EW_LEFT_ABOVE) hh)) THEN
  split (c1091ew_lcy 16384) THENL
   [split (c1091ew_lcx 32768) THENL
     [close C1091EW_RIGHT_LOW_TOP_LOW_IMPOSSIBLE; close C1091ENW_IMPOSSIBLE];
    split (c1091ew_lcx 32768) THENL
     [close C1091EM_IMPOSSIBLE; close C1091EAP_IMPOSSIBLE]]);;

(* Lean: case_excluded *)
let C1091CO_CASE_EXCLUDED = MP C1091RID_EXCLUDES_CASE C1091CO_FAMILY_EXCLUDED;;

(* for the assembly: |- EXCLUDED_ROW 575 *)
let C1091CO_EXCLUDED_ROW = ri_excluded_row 575 C1091CO_CASE_EXCLUDED;;
