(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/LastActual.lean               *)
(* (namespace N12Compact.Completion.OtherCases.C1089.LastActual).  The       *)
(* complete actual-family producer for C1089's last-sector input.            *)
(* Conventions of WallCore.ml / SectorEntrances.ml (owners p i = owner at    *)
(* the literal mask EL i c1089sc_masks; q = c1089od_owners for the           *)
(* structures).  LastSectorRawPoints.Input = c1089lsrp_input and its         *)
(* impossible = C1089LSRE_IMPOSSIBLE; LastSectorNorthwest.Input /            *)
(* ordinary_pair = c1089lsni_input / C1089LSNW_ORDINARY_PAIR;                *)
(* SingletonMissing.zero_missing_points = CCSM_ZERO_MISSING_POINTS (Lean     *)
(* ExactMarkers (maskSupport 1) = OO_MARKERS at mask 1; cap = OO_SIDE_LE);   *)
(* WallOrigins.right_low = OC1089WO_RIGHT_LOW; inside_segment on the         *)
(* vertical segment = OO_VERTICAL_SEGMENT; C981CompletionCrosspoint.point =  *)
(* C981CP_POINT; ElbowPoint.points_original = OCEP_POINTS_ORIGINAL.          *)
(* (Lean header: "Source only".)  Tag C1089LA_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_SectorEntrances.ml";;
needs "n12/geometry/CP_OtherCases_C1089_LastSectorRawEnding.ml";;
needs "n12/geometry/CP_CommonCases_SingletonMissing.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallOrigins.ml";;

let C1089LA_V = C1089WC_V;;
let c1089la_own = c1089wc_own;;
let c1089la_le = c1089se_le;;
let c1089la_apart m n = MP (SPECL C1089LA_V (oo_apart `c1089sc_family` m n)) (c1089wc_hh ());;

(* Lean: stronger_singleton_seeds *)
let C1089LA_STRONGER_SINGLETON_SEEDS = prove
 (c1089wc_stmt [] [mk_neg (c1089la_own 1 `&1` `&1`)]
    (mk_conj(c1089la_own 1 `&91 / &50` `&1`, c1089la_own 1 `&49 / &25` `&19 / &25`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CCSM_ZERO_MISSING_POINTS THEN
  ASM_SIMP_TAC[OO_UNIT; OO_BOX] THEN
  MP_TAC(SPECL C1089LA_V OO_SIDE) THEN MP_TAC(SPECL C1089LA_V OO_SIDE_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  MP_TAC(SPECL (C1089LA_V @ [`c1089sc_family`; `1`]) OO_MARKERS) THEN
  ASM_REWRITE_TAC[in_fam 1 `c1089sc_family`] THEN
  REWRITE_TAC[bitset_bits 1; IN_SET_OF_LIST; MEM]);;

(* the unit-normal hypothesis of the structures, at q = c1089od_owners *)
let c1089la_unit_tm = mk_forall(`i:num`, mk_imp(`i < 12`,
  mk_eq(mk_binop `(+):real->real->real`
          (mk_binop `(*):real->real->real` (mk_comb(el 0 c1089od_owners, `i:num`)) (mk_comb(el 0 c1089od_owners, `i:num`)))
          (mk_binop `(*):real->real->real` (mk_comb(el 1 c1089od_owners, `i:num`)) (mk_comb(el 1 c1089od_owners, `i:num`))),
        `&1`)));;
let C1089LA_UNIT_TAC =
  SUBGOAL_THEN c1089la_unit_tm ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC OO_UNIT THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

(* prove a structure  defn (c1089od_owners)  from the frame, the assumptions and covers *)
let C1089LA_STRUCT_TAC defn covers =
  MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE[c1089od_frame]
           (MP (SPEC_ALL C1089OD_FRAME) (c1089wc_hh ())))) THEN
  DISCH_THEN(fun fr ->
    let frs = CONJUNCTS fr in
    REWRITE_TAC[defn] THEN BETA_TAC THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST (map ACCEPT_TAC frs); REWRITE_TAC[] THEN NO_TAC; ALL_TAC] THEN
    CONV_TAC C1089OD_EL_CONV THEN
    FIRST ([C1089SE_CLOSE_TAC] @
           map (fun th -> MP_TAC (c1089se_cover th) THEN CONV_TAC TAUT) covers));;

(* Lean: input *)
let C1089LA_INPUT = prove
 (c1089wc_stmt [] [c1089la_le (c1089wc_lcy 16384) `&2`; c1089la_le `&2` (c1089wc_lcx 32768)]
    (list_mk_comb(`c1089lsrp_input`, c1089od_owners)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [256; 512; 16384] THEN
  MAP_EVERY (fun (i, p) -> ASSUME_TAC (MP (SPEC_ALL (c1089od_seed i p)) (c1089wc_hh ())))
    [0, (`&1`, `&457 / &500`); 1, (`&3`, `&457 / &500`); 1, (`&1543 / &500`, `&1`);
     2, (`&3`, `&1543 / &500`)] THEN
  ASSUME_TAC (MP (MP (REWRITE_RULE[IMP_CONJ] (SPEC_ALL C1089LA_STRONGER_SINGLETON_SEEDS))
                     (ASSUME C1089WC_NP)) (ASSUME C1089WC_IMG)) THEN
  C1089WC_USE_TAC C1089LA_V C1089WC_SOUTHEAST_INWARD THEN
  C1089WC_USE_TAC C1089LA_V C1089SE_LAST_NE_PAIR THEN
  C1089WC_USE_TAC C1089LA_V C1089SE_LAST_LEFT_PAIR THEN
  C1089WC_USE_TAC C1089LA_V C1089SE_LAST_RIGHT_PAIR THEN
  C1089WC_USE_TAC C1089LA_V C1089DD_BOTTOM_FAR THEN
  C1089WC_USE_TAC C1089LA_V C1089WC_BOTTOM THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&14 / &5`)) (concl th)
    then MP_TAC (SPEC `&113 / &50` th) THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
         REWRITE_TAC[] THEN DISCH_TAC
    else NO_TAC) THEN
  C1089SE_AT_TAC C1089WC_SINGLETON_BAR `&8 / &5` THEN
  C1089SE_AT_TAC C1089WC_TOP_HIGH `&113 / &50` THEN
  (* rightLow, rightMiddle *)
  MAP_EVERY (fun (i, j) -> ASSUME_TAC (c1089la_apart i j)) [16384, 1024; 16384, 512] THEN
  C1089SE_HAVE_TAC (c1089la_own 16384 `&3` `&36 / &25`)
    (C1089WC_APPLY_TAC (SPECL (c1089wc_tuple 16384 @ c1089wc_tuple 1024 @ c1089wc_tuple 512)
                              OC1089WO_RIGHT_LOW)) THEN
  C1089SE_HAVE_TAC (c1089la_own 16384 `&3` `&3 / &2`)
    (MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&8 / &5`] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  (* sSouth *)
  C1089SE_HAVE_TAC (c1089la_own 512 `&2` `&3 / &2`)
    (C1089WC_APPLY_TAC (c1089wc_inst C981CP_POINT (c1089wc_py (c1089wc_tuple 512)))) THEN
  (* aF0, aG0 *)
  C1089SE_HAVE_TAC (c1089la_own 256 `&1` `&87 / &50`)
    (C1089SE_COVER_TAC C1089AC_SOUTHWEST_F_COVER) THEN
  C1089SE_HAVE_TAC (c1089la_own 256 `&1` `&8 / &5`)
   (REFUTE_THEN ASSUME_TAC THEN
    C1089SE_HAVE_TAC (c1089la_own 256 `&87 / &50` `&2`)
      (C1089SE_COVER_TAC C1089AC_SOUTHWEST_G_COVER) THEN
    MP_TAC (c1089wc_inst OCEP_POINTS_ORIGINAL (c1089wc_px (c1089wc_tuple 256))) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089WC_SIDE_TAC; STRIP_TAC] THEN
    C1089WC_CLASH_TAC) THEN
  (* nw := LastSectorNorthwest.ordinary_pair *)
  ASSUME_TAC (CONV_RULE C1089OD_EL_CONV (MP (SPEC `4` (MP (SPEC_ALL C1089SC_ABSENT_MARKER) (c1089wc_hh ())))
                                            (ARITH_RULE `4 < 12`))) THEN
  C1089LA_UNIT_TAC THEN
  SUBGOAL_THEN (list_mk_comb(`c1089lsni_input`, c1089od_owners)) ASSUME_TAC THENL
   [C1089LA_STRUCT_TAC c1089lsni_input [C1089AC_NORTHWEST_F_COVER; C1089AC_NORTHWEST_G_COVER];
    ALL_TAC] THEN
  MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV THENC C1089OD_EL_CONV)
    (MP (SPECL c1089od_owners C1089LSNW_ORDINARY_PAIR)
        (CONJ (ASSUME c1089la_unit_tm) (ASSUME (list_mk_comb(`c1089lsni_input`, c1089od_owners)))))) THEN
  STRIP_TAC THEN
  (* topF7 *)
  C1089SE_HAVE_TAC (mk_neg (c1089la_own 32768 `&8 / &5` `&3`)) (DISCH_TAC THEN C1089WC_CLASH_TAC) THEN
  C1089WC_USE_TAC C1089LA_V C1089DD_TOP_F7 THEN
  (* the input *)
  C1089LA_STRUCT_TAC c1089lsrp_input
    [C1089AC_SOUTHWEST_F_COVER; C1089AC_SOUTHWEST_G_COVER;
     C1089AC_NORTHWEST_F_COVER; C1089AC_NORTHWEST_G_COVER]);;

(* Lean: impossible *)
let C1089LA_IMPOSSIBLE = prove
 (c1089wc_stmt [] [c1089la_le (c1089wc_lcy 16384) `&2`; c1089la_le `&2` (c1089wc_lcx 32768)] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089LA_UNIT_TAC THEN
  MATCH_MP_TAC (SPECL c1089od_owners C1089LSRE_IMPOSSIBLE) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC C1089LA_INPUT THEN ASM_REWRITE_TAC[]);;
