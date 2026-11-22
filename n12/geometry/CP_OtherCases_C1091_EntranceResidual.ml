(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/EntranceResidual.lean         *)
(* (namespace N12Compact.Completion.OtherCases.C1091.EntranceResidual).      *)
(* C1091's actual residual-sector entrance.  Conventions of EntranceWalls.ml *)
(* / EntranceAllPositive.ml (owners p i = owner at the literal mask          *)
(* EL i c1091od_masks; 0 -> 1, 1 -> 12, 4 -> 258).  clockwise_pair =        *)
(* C1089SE_CLOCKWISE_PAIR; DirectDomains.right_pair = C1091DD_RIGHT_PAIR;    *)
(* WallOrigins.right_low = OC1089WO_RIGHT_LOW; C981CompletionCrosspoint.     *)
(* point = C981CP_POINT; SingletonMissing.zero_missing_points =              *)
(* CCSM_ZERO_MISSING_POINTS (ExactMarkers (maskSupport 1) = OO_MARKERS at    *)
(* mask 1, cap = OO_SIDE_LE); SingletonCorner.corner_of_seeds =              *)
(* C1089SC_CORNER_OF_SEEDS; ResidualEntrance / impossible_of_residual_       *)
(* entrance = c1091rp_entrance / C1091RP_IMPOSSIBLE_OF_RESIDUAL_ENTRANCE     *)
(* (q = c1091rp_owners).  (Lean header: "Source only".)  Tag C1091ER_.       *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_EntranceAllPositive.ml";;
needs "n12/geometry/CP_OtherCases_C1091_ResidualProduction.ml";;
needs "n12/geometry/CP_OtherCases_C1089_SingletonCorner.ml";;
needs "n12/geometry/CP_CommonCases_SingletonMissing.ml";;

(* Lean: clockwise_pair (abbrev of C1089.SectorEntrances.clockwise_pair) *)
let C1091ER_CLOCKWISE_PAIR = C1089SE_CLOCKWISE_PAIR;;

(* Lean: northeast_pair *)
let C1091ER_NORTHEAST_PAIR = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcy 16384) `&2`; c1091ew_le `&2` (c1091ew_lcx 32768)]
    (mk_conj(c1091ew_own 1024 `&3` `&113 / &50`, c1091ew_own 1024 `&3` `&12 / &5`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [1024] THEN
  C1091EW_USE_TAC C1091EW_V C1091EW_SOUTHEAST_INWARD THEN
  C1091EW_CHORDS_TAC C1091EW_TOP_HIGH [`&113 / &50`; `&239 / &100`] THEN
  C1091EAP_HAVE_TAC (c1091ew_own 1024 `&3` `&12 / &5`)
    (C1091EAP_COVER_TAC C1091ED_NORTHEAST_G) THEN
  ASSUME_TAC (c1091eap_cover C1091ED_NORTHEAST_F) THEN
  ASM_REWRITE_TAC[] THEN
  C1091EAP_APPLY_TAC (c1089wc_inst C1091ER_CLOCKWISE_PAIR (c1089wc_sw (c1091ew_tuple 1024))));;

(* Lean: right_pair *)
let C1091ER_RIGHT_PAIR = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcy 16384) `&2`; c1091ew_le `&2` (c1091ew_lcx 32768)]
    (mk_conj(c1091ew_own 16384 `&3` `&87 / &50`, c1091ew_own 16384 `&3` `&8 / &5`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_NORTHEAST_PAIR THEN
  C1091EW_USE_TAC C1091EW_V C1091DD_RIGHT_PAIR THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: southeast_south *)
let C1091ER_SOUTHEAST_SOUTH = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcy 16384) `&2`; c1091ew_le `&2` (c1091ew_lcx 32768)]
    (c1091ew_own 512 `&2` `&3 / &2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [512; 16384] THEN
  C1091EW_USE_TAC C1091EW_V C1091EW_SOUTHEAST_INWARD THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_NORTHEAST_PAIR THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_RIGHT_PAIR THEN
  C1091EAP_HAVE_TAC (c1091ew_own 16384 `&3` `&36 / &25`)
    (C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 16384 @ c1091ew_tuple 1024 @ c1091ew_tuple 512)
                               OC1089WO_RIGHT_LOW)) THEN
  C1091EAP_HAVE_TAC (c1091ew_own 16384 `&3` `&3 / &2`)
    (MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&8 / &5`] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  C1091EAP_APPLY_TAC (c1089wc_inst C981CP_POINT (c1089wc_py (c1091ew_tuple 512))));;

(* Lean: stronger_singleton_seeds *)
let C1091ER_STRONGER_SINGLETON_SEEDS = prove
 (c1091ew_stmt [] [mk_neg (c1091ew_own 1 `&1` `&1`)]
    (mk_conj(c1091ew_own 1 `&91 / &50` `&1`, c1091ew_own 1 `&49 / &25` `&19 / &25`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CCSM_ZERO_MISSING_POINTS THEN
  ASM_SIMP_TAC[OO_UNIT; OO_BOX] THEN
  MP_TAC(SPECL C1091EW_V OO_SIDE) THEN MP_TAC(SPECL C1091EW_V OO_SIDE_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  MP_TAC(SPECL (C1091EW_V @ [`c1091od_family`; `1`]) OO_MARKERS) THEN
  ASM_REWRITE_TAC[in_fam 1 `c1091od_family`] THEN
  REWRITE_TAC[bitset_bits 1; IN_SET_OF_LIST; MEM]);;

(* Lean: singleton_corner *)
let C1091ER_SINGLETON_CORNER = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcy 16384) `&2`; c1091ew_le `&2` (c1091ew_lcx 32768)]
    (c1091ew_own 1 `&1` `&1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [1; 12; 512; 1024; 8192; 16384] THEN
  REFUTE_THEN ASSUME_TAC THEN
  ASSUME_TAC (MP (SPEC_ALL (c1091od_seed 0 (`&1`, `&457 / &500`))) (c1091ew_hh ())) THEN
  ASSUME_TAC (MP (SPEC_ALL (c1091od_seed 1 (`&3`, `&457 / &500`))) (c1091ew_hh ())) THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_STRONGER_SINGLETON_SEEDS THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_SOUTHEAST_SOUTH THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_NORTHEAST_PAIR THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_RIGHT_PAIR THEN
  ASSUME_TAC (MP (SPEC_ALL C1091ED_BOTTOM_FAR) (c1091ew_hh ())) THEN
  MP_TAC (MP (SPEC_ALL C1091ED_BOTTOM_BAR) (c1091ew_hh ())) THEN STRIP_TAC THEN
  C1091EAP_HAVE_TAC (c1091ew_own 1 `&1` `&1`)
    (C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 1 @ c1091ew_tuple 12 @ c1091ew_tuple 512 @
                                c1091ew_tuple 1024 @ c1091ew_tuple 8192 @ c1091ew_tuple 16384)
                               C1089SC_CORNER_OF_SEEDS)) THEN
  C1091EAP_CLOSE_TAC);;

(* Lean: input_of_northwest *)
let C1091ER_INPUT_OF_NORTHWEST = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcy 16384) `&2`; c1091ew_le `&2` (c1091ew_lcx 32768);
                   c1091ew_own 2048 `&8 / &5` `&3`]
    (list_mk_comb(`c1091rp_entrance`, c1091rp_owners)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_SINGLETON_CORNER THEN
  C1091EW_USE_TAC C1091EW_V C1091EW_SOUTHEAST_INWARD THEN
  C1091EW_USE_TAC C1091EW_V C1091ER_NORTHEAST_PAIR THEN
  ASSUME_TAC (MP (SPEC_ALL OC1091EML_ORIGINAL) (c1091ew_hh ())) THEN
  REWRITE_TAC[c1091rp_entrance] THEN BETA_TAC THEN CONV_TAC C1091RP_EL_CONV THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: impossible_of_northwest *)
let C1091ER_IMPOSSIBLE_OF_NORTHWEST = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcy 16384) `&2`; c1091ew_le `&2` (c1091ew_lcx 32768);
                   c1091ew_own 2048 `&8 / &5` `&3`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPEC_ALL C1091RP_IMPOSSIBLE_OF_RESIDUAL_ENTRANCE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1091ER_INPUT_OF_NORTHWEST THEN ASM_REWRITE_TAC[]);;
