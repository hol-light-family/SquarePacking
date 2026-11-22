(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/EntranceNorthwest.lean        *)
(* (namespace N12Compact.Completion.OtherCases.C1091.EntranceNorthwest).     *)
(* Reconstruction of the missing northwest F3 entrance.  Conventions of      *)
(* EntranceWalls.ml / EntranceResidual.ml (owners p i = owner at the literal *)
(* mask EL i c1091od_masks: 0 -> 1, 4 -> 258, 5 -> 512, 6 -> 1024,          *)
(* 7 -> 2048, 8 -> 4096, 10 -> 16384, 11 -> 32768); frame fields via         *)
(* C1091EW_BASE_TAC (seeds) / oo_apart (C1091EW_CLASH_TAC).                  *)
(* EntranceMergedShallow.original_points C1091EMS_ORIGINAL_POINTS;           *)
(* EntranceNorthwestPoints.merged_alternative_original / northwest_low       *)
(* C1091ENP_*; EntranceResidual singleton_corner / impossible_of_northwest   *)
(* C1091ER_*; EntranceDomains left_pair / northwest_f / northwest_g          *)
(* C1091ED_*; southeast_center C1091EW_SOUTHEAST_CENTER;                     *)
(* InwardPoint.strong_original CCIP_STRONG_ORIGINAL (at pullY (pullX q));    *)
(* ElbowPoint.points_original OCEP_POINTS_ORIGINAL (at pullSwap q).          *)
(* (Lean header: "Source only".)  Tag C1091ENW_.                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_EntranceMergedShallow.ml";;
needs "n12/geometry/CP_OtherCases_C1091_EntranceNorthwestPoints.ml";;
needs "n12/geometry/CP_OtherCases_C1091_EntranceResidual.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;

let C1091ENW_HYPS = [c1091ew_le (c1091ew_lcy 16384) `&2`; c1091ew_le `&2` (c1091ew_lcx 32768)];;

(* Lean: merged_points *)
let C1091ENW_MERGED_POINTS = prove
 (c1091ew_stmt [] C1091ENW_HYPS
    (list_mk_conj [c1091ew_own 258 `&73 / &50` `&199 / &100`; c1091ew_own 258 `&3 / &2` `&2`;
                   c1091ew_own 258 `&79 / &50` `&2`]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [258] THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_SINGLETON_CORNER THEN
  ASSUME_TAC (MP (SPEC_ALL (c1091od_seed 4 (`&457 / &500`, `&1`))) (c1091ew_hh ())) THEN
  C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 258) C1091EMS_ORIGINAL_POINTS));;

(* Lean: northwest_f3 *)
let C1091ENW_NORTHWEST_F3 = prove
 (c1091ew_stmt [] C1091ENW_HYPS (c1091ew_own 2048 `&8 / &5` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [258; 2048] THEN
  ASSUME_TAC (MP (SPEC_ALL (c1091od_seed 4 (`&457 / &500`, `&1`))) (c1091ew_hh ())) THEN
  MP_TAC (MP (SPEC_ALL C1091ED_LEFT_PAIR) (c1091ew_hh ())) THEN STRIP_TAC THEN
  C1091EW_USE_TAC C1091EW_V C1091ENW_MERGED_POINTS THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_SINGLETON_CORNER THEN
  REFUTE_THEN ASSUME_TAC THEN
  C1091EAP_HAVE_TAC (c1091ew_own 2048 `&2` `&113 / &50`)
    (C1091EAP_COVER_TAC C1091ED_NORTHWEST_F) THEN
  ASM_CASES_TAC (c1091ew_own 2048 `&87 / &50` `&2`) THENL
   [C1091EAP_HAVE_TAC (c1091ew_own 2048 `&73 / &50` `&201 / &100`)
      (C1091EAP_APPLY_TAC (c1089wc_inst CCIP_STRONG_ORIGINAL (c1089wc_py (c1089wc_px (c1091ew_tuple 2048))))) THEN
    MP_TAC (SPECL (c1091ew_tuple 258) C1091ENP_MERGED_ALTERNATIVE_ORIGINAL) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1091EAP_SIDE_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
     [C1091EW_USE_TAC C1091EW_V C1091EW_SOUTHEAST_CENTER THEN
      C1091EAP_HAVE_TAC (c1091ew_own 2048 `&8 / &5` `&2`)
        (C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 2048) C1091ENP_NORTHWEST_LOW)) THEN
      C1091EW_CLASH_TAC;
      C1091EW_CLASH_TAC];
    C1091EAP_HAVE_TAC (c1091ew_own 2048 `&87 / &50` `&3`)
      (C1091EAP_COVER_TAC C1091ED_NORTHWEST_G) THEN
    MP_TAC (c1089wc_inst OCEP_POINTS_ORIGINAL (c1089wc_sw (c1091ew_tuple 2048))) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1091EAP_SIDE_TAC; STRIP_TAC] THEN
    C1091EW_CLASH_TAC]);;

(* Lean: impossible *)
let C1091ENW_IMPOSSIBLE = prove
 (c1091ew_stmt [] C1091ENW_HYPS `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPEC_ALL C1091ER_IMPOSSIBLE_OF_NORTHWEST) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (SPEC_ALL C1091ENW_NORTHWEST_F3) THEN ASM_REWRITE_TAC[]);;
