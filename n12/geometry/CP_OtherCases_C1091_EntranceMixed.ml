(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/EntranceMixed.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C1091.EntranceMixed).  The    *)
(* C1091 closed (++,-) sector.  Conventions of EntranceWalls.ml /            *)
(* EntranceAllPositive.ml (owners p i = owner at the literal mask            *)
(* EL i c1091od_masks; 4 -> 258 merged).  clockwise_pair =                   *)
(* C1089SE_CLOCKWISE_PAIR; WallOrigins.top_left_advance =                    *)
(* OC1089WO_TOP_LEFT_ADVANCE; inside_segment on the horizontal segment =     *)
(* OO_HORIZONTAL_SEGMENT; C981CompletionCrosspoint.point = C981CP_POINT;     *)
(* InwardPoint.strong_original = CCIP_STRONG_ORIGINAL; EntranceMergedLow.    *)
(* alternative_original = OC1091EML_ALTERNATIVE_ORIGINAL.                    *)
(* (Lean header: "Source only".)  Tag C1091EM_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_EntranceAllPositive.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;

(* Lean: clockwise_pair (abbrev of C1089.SectorEntrances.clockwise_pair) *)
let C1091EM_CLOCKWISE_PAIR = C1089SE_CLOCKWISE_PAIR;;

(* Lean: northeast_pair *)
let C1091EM_NORTHEAST_PAIR = prove
 (c1091ew_stmt [] [c1091ew_le `&2` (c1091ew_lcy 4096); c1091ew_le `&2` (c1091ew_lcy 16384);
                   c1091ew_le (c1091ew_lcx 32768) `&2`]
    (mk_conj(c1091ew_own 1024 `&12 / &5` `&3`, c1091ew_own 1024 `&113 / &50` `&3`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [1024] THEN
  C1091EW_USE_TAC C1091EW_V C1091EW_NORTHWEST_INWARD THEN
  C1091EW_CHORDS_TAC C1091EW_RIGHT_HIGH [`&113 / &50`; `&239 / &100`] THEN
  C1091EAP_HAVE_TAC (c1091ew_own 1024 `&12 / &5` `&3`)
    (C1091EAP_COVER_TAC C1091ED_NORTHEAST_F) THEN
  ASSUME_TAC (c1091eap_cover C1091ED_NORTHEAST_G) THEN
  ASM_REWRITE_TAC[] THEN
  C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 1024) C1091EM_CLOCKWISE_PAIR));;

(* Lean: impossible *)
let C1091EM_IMPOSSIBLE = prove
 (c1091ew_stmt [] [c1091ew_le `&2` (c1091ew_lcy 16384); c1091ew_le (c1091ew_lcx 32768) `&2`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [2048; 32768] THEN
  ASSUME_TAC (MATCH_MP REAL_LT_IMP_LE (MP (SPEC_ALL C1091EW_LEFT_ABOVE) (c1091ew_hh ()))) THEN
  C1091EW_USE_TAC C1091EW_V C1091EW_NORTHWEST_INWARD THEN
  C1091EW_USE_TAC C1091EW_V C1091EM_NORTHEAST_PAIR THEN
  (* topF3, missingF3 *)
  MP_TAC (c1091eap_cover C1091ED_TOP_COMPONENT) THEN STRIP_TAC THENL [C1091EW_CLASH_TAC; ALL_TAC] THEN
  C1091EAP_HAVE_TAC (mk_neg (c1091ew_own 2048 `&8 / &5` `&3`)) (DISCH_TAC THEN C1091EW_CLASH_TAC) THEN
  (* topLow, topMiddle *)
  C1091EAP_HAVE_TAC (c1091ew_own 32768 `&36 / &25` `&3`)
    (C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 32768 @ c1091ew_tuple 1024 @ c1091ew_tuple 2048)
                               OC1089WO_TOP_LEFT_ADVANCE)) THEN
  C1091EAP_HAVE_TAC (c1091ew_own 32768 `&3 / &2` `&3`)
    (MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&8 / &5`] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  (* halfpoint, strong *)
  C1091EAP_HAVE_TAC (c1091ew_own 2048 `&3 / &2` `&2`)
    (C1091EAP_APPLY_TAC (c1089wc_inst C981CP_POINT (c1089wc_sw (c1089wc_px (c1091ew_tuple 2048))))) THEN
  C1091EAP_HAVE_TAC (c1091ew_own 2048 `&73 / &50` `&201 / &100`)
    (C1091EAP_APPLY_TAC (c1089wc_inst CCIP_STRONG_ORIGINAL (c1089wc_py (c1089wc_px (c1091ew_tuple 2048))))) THEN
  MP_TAC (MP (SPEC_ALL OC1091EML_ALTERNATIVE_ORIGINAL) (c1091ew_hh ())) THEN
  STRIP_TAC THEN C1091EW_CLASH_TAC);;
