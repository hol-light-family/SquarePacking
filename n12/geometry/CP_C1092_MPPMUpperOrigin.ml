(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMUpperOrigin.lean                     *)
(* (N12Compact.C1092MPPMUpperOrigin).  The northeast ordinary halfpoint and  *)
(* the original top-wall origin in the one-omission entrance.  Conventions   *)
(* and forward toolkit of CP_C1092_MPPMOmissionCenter.ml (c1092moc_          *)
(* functions; owners p i at mask EL i c1092wc_code, side l; WallContext p    *)
(* mppm is C1092MPPE_CTX, omitted is C1092MPPE_OMIT).  The private side_gt / *)
(* side_same / marker_point are C1092MOC_SIDE_GT / SIDE_SAME / MARKER_POINT  *)
(* (markers through oo_seed); translate / pullX / pullY via                  *)
(* C1092RC_INSIDE_TRANSLATE / LINSIDE_PULLX / LINSIDE_PULLY (c1092moc_layers);*)
(* containers via LCONT_PULLX / PULLY.  MMMPMarkerHalfpoint.point            *)
(* C1092MMH_POINT; WallProfile.boundary_origin OCWPBO_BOUNDARY_ORIGIN;       *)
(* MPPMPointCore.rectangle C1092MPC_RECTANGLE; MPPMRightInner.other_ordinary *)
(* C1092MPRI_OTHER_ORDINARY; OriginalOwners.horizontal_segment               *)
(* OO_HORIZONTAL_SEGMENT.  Tag C1092MPUO_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMRightInner.ml";;
needs "n12/geometry/CP_C1092_MMMP_MarkerHalfpoint.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/CP_C1092_MPPMTopOrigin.ml";;
needs "n12/geometry/CP_C1092_MPPMPointCore.ml";;

(* Lean: northeast_halfpoint *)
let c1092mpuo_northeast_halfpoint () =
  let pair = CONJUNCT1 (c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS) in
  let wa = c1092moc_use C1092MPPE_WALL_AUXILIARIES in
  let mid = c1092mpus_core `&113 / &50` `&2` in
  let t, eqs = c1092moc_layers 6 [C1092MOC_Y; c1092moc_tr `&2` `&2`] in
  let conv = c1092moc_conv eqs in
  let h = c1092moc_apply conv (SPECL (t @ [`&43 / &500`]) C1092MMH_POINT)
    [c1092moc_punit 6 t; c1092moc_pos (); c1092moc_side ();
     c1092moc_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT1 pair; CONJUNCT2 pair;
     c1092moc_excl 6 5 mid;
     c1092moc_excl 6 10 (c1092moc_seed 10 (`&1543 / &500`, `&2`));
     c1092moc_excl 6 2 (c1092moc_seed 2 (`&3`, `&3`));
     c1092moc_excl 6 11 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 wa)))] in
  h;;
let C1092MPUO_NORTHEAST_HALFPOINT =
  c1092moc_close 6 "&3" "&5 / &2" (c1092mpuo_northeast_halfpoint ());;

(* Lean: top_origin *)
let c1092mpuo_top_origin () =
  let layers = [C1092MOC_X; C1092MOC_Y] in
  let tB, eqB = c1092moc_layers 11 layers and tK, eqK = c1092moc_layers 2 layers in
  let other = CONJUNCT2 (c1092moc_use C1092MPRI_OTHER_ORDINARY) in
  let half = c1092moc_use C1092MPUO_NORTHEAST_HALFPOINT in
  let disj =
    let tm = list_mk_comb(`ldisj`, tK @ tB) in
    let eq = (REWRITE_CONV[ldisj] THENC c1092moc_unfold (eqK @ eqB)) tm in
    EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real`
      (SPECL [`&4 - x`; `&4 - y`] (c1092moc_apart 2 11)))) in
  c1092moc_apply (c1092moc_conv (eqB @ eqK))
    (SPECL (tB @ tK @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN)
    [c1092moc_punit 11 tB; c1092moc_punit 2 tK; c1092moc_pos (); c1092moc_side (); REFL `l:real`;
     MATCH_MP C1092MTO_BOX_Y (c1092moc_plcont 11 layers);
     MATCH_MP C1092MTO_BOX_XY (c1092moc_plcont 2 layers);
     c1092moc_seed 11 (`&2`, `&1543 / &500`); other;
     c1092moc_seed 2 (`&3`, `&1543 / &500`); c1092moc_seed 2 (`&3`, `&3`);
     c1092moc_excl 2 6 half; disj];;
let C1092MPUO_TOP_ORIGIN = c1092moc_close 11 "&2" "&3" (c1092mpuo_top_origin ());;

(* Lean: top_segment *)
let C1092MPUO_TOP_SEGMENT = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> !x. &2 <= x ==> x <= &12 / &5 ==> %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT (c1092mppe_in 11 "x" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&2`; `&12 / &5`] THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPUO_TOP_ORIGIN) THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPRI_OTHER_ORDINARY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
