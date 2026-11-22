(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ReversePrefix.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C1089.Reverse).  The reverse- *)
(* cycle entrance on the actual unmerged C1089 owners.                       *)
(* Conventions of OriginalData.ml / WallCore.ml: q : Fin 12 -> OpenSquare is *)
(* qc qs qu qv qa : num -> real; owners p is c1089od_owners (owner at mask   *)
(* EL i c1089sc_masks, literal masks 0 -> 1, 3 -> 192, 4 -> 256, 5 -> 512,  *)
(* 6 -> 1024, 7 -> 2048, 8 -> 4096, 9 -> 8192, 10 -> 16384, 11 -> 32768).    *)
(* The structure PointTable (extends Frame) is c1089rp_point_table.          *)
(* Used: C1092MixedSpan / C1092CornerTwoGaps .impossible = C1092MS_ /        *)
(* C1092CTG_IMPOSSIBLE, WallLowerReach.point = WLR_POINT,                    *)
(* WallUpperMissingReach.point = WUMR_POINT, C981CompletionCrosspoint.point  *)
(* = C981CP_POINT, ElbowPoint.points_original = OCEP_POINTS_ORIGINAL,        *)
(* NESelectionOwners.selection = C1090NESO_SELECTION, WallOrigins.           *)
(* top_origin_from_northwest = OC1089WO_TOP_ORIGIN_FROM_NORTHWEST,           *)
(* vertical_segment = OO_VERTICAL_SEGMENT.  (Lean header: "Source only".)    *)
(* Tag C1089RP_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_OriginalData.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallCore.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallOrigins.ml";;
needs "n12/geometry/CP_OtherCases_C1090_NESelectionOwners.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;

(* the PointTable fields (beyond Frame), for a point builder own i x y *)
let c1089rp_fields own =
  let pt i x y = own i x y in
  list_mk_conj
   [pt 4 `&2` `&87 / &50`; pt 4 `&87 / &50` `&2`; pt 4 `&2` `&3 / &2`; pt 4 `&3 / &2` `&2`;
    pt 5 `&3` `&87 / &50`; pt 5 `&3` `&8 / &5`;
    list_mk_disj [pt 6 `&2` `&113 / &50`; pt 6 `&12 / &5` `&3`; pt 6 `&3` `&113 / &50`];
    pt 6 `&113 / &50` `&3`;
    pt 7 `&1` `&113 / &50`; pt 7 `&1` `&12 / &5`;
    pt 8 `&1` `&87 / &50`; pt 8 `&1` `&8 / &5`;
    pt 9 `&12 / &5` `&1`; pt 9 `&113 / &50` `&1`; pt 9 `&14 / &5` `&1`;
    mk_forall(`x:real`, mk_imp(`&113 / &50 <= x`, mk_imp(`x <= &14 / &5`, pt 9 `x:real` `&1`)));
    pt 10 `&3` `&113 / &50`; pt 10 `&3` `&12 / &5`; pt 10 `&3` `&64 / &25`;
    mk_forall(`y:real`, mk_imp(`&113 / &50 <= y`, mk_imp(`y <= &64 / &25`, pt 10 `&3` `y:real`)));
    pt 11 `&8 / &5` `&3`; pt 11 `&87 / &50` `&3`; pt 11 `&2` `&3`];;

let c1089rp_qown i x y =
  let n = mk_small_numeral i in
  list_mk_comb(`linside`, map (fun f -> mk_comb(f, n))
    [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`] @ [x; y]);;

(* Lean: PointTable (structure, extends Frame) *)
let c1089rp_point_table = new_definition
  (mk_eq(list_mk_comb(mk_var("c1089rp_point_table", `:(num->real)->(num->real)->(num->real)->(num->real)->(num->real)->bool`),
                       [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`]),
         mk_conj(`c1089od_frame qc qs qu qv qa`, c1089rp_fields c1089rp_qown)));;

(* ------------------------------------------------------------------------- *)
(* proof helpers                                                             *)
(* ------------------------------------------------------------------------- *)

let C1089RP_V = C1089WC_V;;
let c1089rp_own i = c1089wc_own (el i C1089WC_MASKS);;
let c1089rp_np () = ASSUME C1089WC_NP;;
let c1089rp_tuple i = c1089wc_tuple (el i C1089WC_MASKS);;
let c1089rp_box i = MP (SPECL (C1089RP_V @ [mk_small_numeral (el i C1089WC_MASKS)]) OO_BOX) (c1089rp_np ());;
let c1089rp_cover th = MP (SPEC_ALL (c1089wc_lit th)) (c1089wc_hh ());;
let c1089rp_apart i j =
  MP (SPECL C1089RP_V (oo_apart `c1089sc_family` (el i C1089WC_MASKS) (el j C1089WC_MASKS))) (c1089wc_hh ());;

let C1089RP_HAVE_TAC tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;

(* close a goal from an assumption, a clash of two owners, or a refuted assumption *)
let C1089RP_CLOSE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC; C1089WC_CLASH_TAC;
         FIRST_ASSUM(fun th -> if is_neg (concl th) then
           FIRST_ASSUM(fun th2 -> CONTR_TAC (MP (NOT_ELIM th) th2)) else NO_TAC)];;

(* case split on an actual cover *)
let C1089RP_COVER_TAC th =
  MP_TAC (c1089rp_cover th) THEN STRIP_TAC THEN C1089RP_CLOSE_TAC;;

(* instance of a chord / segment lemma at a coordinate, as an assumption *)
let C1089RP_AT_TAC th t =
  MP_TAC (SPECL (C1089RP_V @ [t]) th) THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let C1089RP_SEEDS =
  [1, (`&1543 / &500`, `&1`); 3, (`&1`, `&1543 / &500`)];;

(* ------------------------------------------------------------------------- *)
(* the points                                                                *)
(* ------------------------------------------------------------------------- *)

let C1089RP_POINTS = prove
 (c1089wc_stmt []
    [mk_binop `(<=):real->real->bool` (c1089wc_lcy 4096) `&2`;
     mk_binop `(<=):real->real->bool` (c1089wc_lcx 32768) `&2`]
    (c1089rp_fields c1089rp_own),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1089WC_BASE_TAC [192; 256; 512; 1024; 2048; 4096; 8192; 16384; 32768] THEN
  MAP_EVERY (fun (i, p) -> ASSUME_TAC (MP (SPEC_ALL (c1089od_seed i p)) (c1089wc_hh ()))) C1089RP_SEEDS THEN
  (* a := southwest_inward, topG4, the top chord at 161/100 *)
  C1089WC_USE_TAC C1089RP_V C1089WC_SOUTHWEST_INWARD THEN
  C1089RP_AT_TAC C1089WC_TOP_LOW `&87 / &50` THEN
  C1089RP_AT_TAC C1089WC_TOP_LOW `&161 / &100` THEN
  (* ng1 *)
  C1089RP_HAVE_TAC (c1089rp_own 7 `&1` `&12 / &5`)
    (C1089RP_COVER_TAC C1089AC_NORTHWEST_G_COVER) THEN
  (* nf1 *)
  C1089RP_HAVE_TAC (c1089rp_own 7 `&1` `&113 / &50`)
   (REFUTE_THEN ASSUME_TAC THEN
    C1089RP_HAVE_TAC (c1089rp_own 7 `&8 / &5` `&3`)
     (REFUTE_THEN ASSUME_TAC THEN
      C1089RP_HAVE_TAC (c1089rp_own 7 `&2` `&113 / &50`)
        (C1089RP_COVER_TAC C1089AC_NORTHWEST_F_COVER) THEN
      C1089WC_REFUTE_TAC (c1089wc_inst C1092MS_IMPOSSIBLE (c1089wc_py (c1089wc_px (c1089rp_tuple 7))))) THEN
    C1089WC_REFUTE_TAC (c1089wc_inst C1092CTG_IMPOSSIBLE
      (c1089wc_px (c1089rp_tuple 7) @ [`&39 / &100`; `&13 / &50`]))) THEN
  (* lf0, lg0 *)
  C1089RP_AT_TAC C1089WC_LEFT_LOW `&87 / &50` THEN
  C1089RP_HAVE_TAC (c1089rp_own 8 `&1` `&8 / &5`)
    (C1089RP_COVER_TAC C1089AC_LEFT_G_COVER) THEN
  (* lowLeft, leftBar at 8/5 and 3/2 *)
  ASSUME_TAC (MATCH_MP LCONT_PULLY (c1089rp_box 8)) THEN
  C1089RP_HAVE_TAC (c1089rp_own 8 `&1` `&36 / &25`)
    (C1089WC_APPLY_TAC (c1089wc_inst WLR_POINT (c1089wc_py (c1089rp_tuple 8)))) THEN
  MAP_EVERY (fun y ->
    C1089RP_HAVE_TAC (c1089rp_own 8 `&1` y)
     (MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&87 / &50`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV)) [`&8 / &5`; `&3 / &2`] THEN
  (* aSouth *)
  C1089RP_HAVE_TAC (c1089rp_own 4 `&2` `&3 / &2`)
    (C1089WC_APPLY_TAC (c1089wc_inst C981CP_POINT (c1089wc_py (c1089wc_px (c1089rp_tuple 4))))) THEN
  (* aWest, singleton bar at 8/5 and 3/2 *)
  C1089RP_AT_TAC C1089WC_SINGLETON_BAR `&8 / &5` THEN
  C1089RP_AT_TAC C1089WC_SINGLETON_BAR `&3 / &2` THEN
  C1089RP_HAVE_TAC (c1089rp_own 4 `&3 / &2` `&2`)
    (C1089WC_APPLY_TAC (c1089wc_inst C981CP_POINT
       (c1089wc_sw (c1089wc_py (c1089wc_px (c1089rp_tuple 4)))))) THEN
  (* bottom facts *)
  C1089WC_USE_TAC C1089RP_V C1089DD_BOTTOM_FAR THEN
  C1089WC_USE_TAC C1089RP_V C1089WC_BOTTOM THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&14 / &5`)) (concl th)
    then MP_TAC (SPEC `&113 / &50` th) THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
         REWRITE_TAC[] THEN DISCH_TAC
    else NO_TAC) THEN
  (* sf8 *)
  C1089RP_HAVE_TAC (c1089rp_own 5 `&3` `&87 / &50`)
    (C1089RP_COVER_TAC C1089AC_SOUTHEAST_F_COVER) THEN
  (* sg8 *)
  C1089RP_HAVE_TAC (c1089rp_own 5 `&3` `&8 / &5`)
   (REFUTE_THEN ASSUME_TAC THEN
    C1089RP_HAVE_TAC (c1089rp_own 5 `&113 / &50` `&2`)
      (C1089RP_COVER_TAC C1089AC_SOUTHEAST_G_COVER) THEN
    MP_TAC (SPECL (c1089rp_tuple 5) OCEP_POINTS_ORIGINAL) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089WC_SIDE_TAC; STRIP_TAC] THEN
    C1089WC_CLASH_TAC) THEN
  (* r := right_high_pair *)
  C1089RP_HAVE_TAC (mk_neg (c1089rp_own 10 `&3` `&87 / &50`)) (DISCH_TAC THEN C1089WC_CLASH_TAC) THEN
  C1089WC_USE_TAC C1089RP_V C1089DD_RIGHT_HIGH_PAIR THEN
  (* eg7 via NESelectionOwners.selection *)
  MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE[c1089od_frame]
           (MP (SPEC_ALL C1089OD_FRAME) (c1089wc_hh ())))) THEN
  DISCH_THEN(fun fr ->
    let c1089rp_fside = CONJUNCT1 fr and c1089rp_fapart = find (fun th -> can (find_term ((=) `~(i:num = j)`)) (concl th)) (CONJUNCTS fr) in
    let data_tm = list_mk_comb(`c1090neso_data`, c1089od_owners) in
    let unit_tm = mk_forall(`i:num`, mk_imp(`i < 12`,
       mk_eq(mk_binop `(+):real->real->real`
               (mk_binop `(*):real->real->real` (mk_comb(el 0 c1089od_owners, `i:num`)) (mk_comb(el 0 c1089od_owners, `i:num`)))
               (mk_binop `(*):real->real->real` (mk_comb(el 1 c1089od_owners, `i:num`)) (mk_comb(el 1 c1089od_owners, `i:num`))),
             `&1`))) in
    SUBGOAL_THEN unit_tm ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC OO_UNIT THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN data_tm ASSUME_TAC THENL
     [REWRITE_TAC[c1090neso_data] THEN BETA_TAC THEN REPEAT CONJ_TAC THEN
      FIRST [ACCEPT_TAC c1089rp_fside; ACCEPT_TAC c1089rp_fapart; ALL_TAC] THEN
      CONV_TAC C1089OD_EL_CONV THEN
      FIRST [C1089RP_CLOSE_TAC;
             MP_TAC (c1089rp_cover C1089AC_NORTHEAST_F_COVER) THEN
               STRIP_TAC THEN ASM_REWRITE_TAC[] THEN C1089WC_CLASH_TAC;
             MP_TAC (c1089rp_cover C1089AC_NORTHEAST_G_COVER) THEN
               STRIP_TAC THEN ASM_REWRITE_TAC[] THEN C1089WC_CLASH_TAC];
      ALL_TAC] THEN
    MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV THENC C1089OD_EL_CONV)
      (MP (SPECL c1089od_owners C1090NESO_SELECTION)
         (CONJ (ASSUME unit_tm) (ASSUME data_tm)))) THEN
    STRIP_TAC) THEN
  (* tf3 *)
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089DD_TOP_COMPONENT))) THEN
  STRIP_TAC THENL [C1089WC_CLASH_TAC; ALL_TAC] THEN
  (* rAdvance, rightBar *)
  ASSUME_TAC (MATCH_MP LCONT_PULLX (c1089rp_box 10)) THEN
  C1089RP_HAVE_TAC (c1089rp_own 10 `&3` `&64 / &25`)
    (C1089WC_APPLY_TAC (c1089wc_inst WUMR_POINT (c1089wc_px (c1089rp_tuple 10)))) THEN
  (* topOrigin *)
  MAP_EVERY (fun (i, j) -> ASSUME_TAC (c1089rp_apart i j))
    [7, 4; 7, 8; 7, 3; 7, 11; 3, 7; 3, 11] THEN
  C1089RP_HAVE_TAC (c1089rp_own 11 `&2` `&3`)
    (C1089WC_APPLY_TAC (SPECL (c1089rp_tuple 7 @ c1089rp_tuple 4 @ c1089rp_tuple 8 @
                               c1089rp_tuple 11 @ c1089rp_tuple 3)
                              OC1089WO_TOP_ORIGIN_FROM_NORTHWEST)) THEN
  (* the table *)
  REPEAT CONJ_TAC THEN
  FIRST [C1089RP_CLOSE_TAC;
         FIRST_ASSUM ACCEPT_TAC;
         MP_TAC (c1089rp_cover C1089AC_NORTHEAST_F_COVER) THEN CONV_TAC TAUT;
         REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
           MAP_EVERY EXISTS_TAC [`&113 / &50`; `&64 / &25`] THEN
           ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* Lean: point_table *)
let C1089RP_POINT_TABLE = prove
 (c1089wc_stmt []
    [mk_binop `(<=):real->real->bool` (c1089wc_lcy 4096) `&2`;
     mk_binop `(<=):real->real->bool` (c1089wc_lcx 32768) `&2`]
    (list_mk_comb(`c1089rp_point_table`, c1089od_owners)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1089rp_point_table] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C1089OD_FRAME THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN CONV_TAC C1089OD_EL_CONV THEN
    MATCH_MP_TAC C1089RP_POINTS THEN ASM_REWRITE_TAC[]]);;
