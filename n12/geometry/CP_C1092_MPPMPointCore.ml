(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPointCore.lean                       *)
(* (namespace N12Compact.C1092MPPMPointCore).  Point core and full strict    *)
(* rectangle for the MPPM bottom-omission owner.  Conventions and forward    *)
(* toolkit of CP_C1092_MPPMOmissionCenter.ml (the c1092moc_ functions;       *)
(* owners p i at mask EL i c1092wc_code: 4 -> 256, 5 -> 512, 6 -> 1024,      *)
(* 9 -> 8192, 10 -> 16384).  The private side_gt / side_cap / chart /        *)
(* inside_chart / center_chart / marker_point are those of MPPMOmissionCenter*)
(* (C1092MOC_ names).  inside_segment / horizontal_segment / vertical_segment =   *)
(* OO_VERTICAL_SEGMENT / OO_HORIZONTAL_SEGMENT, C981CompletionCrosspoint.    *)
(* point = C981CP_POINT, InwardCenterDiagonal.point / long_point =           *)
(* C1092ICD_POINT / C1092ICD_LONG_POINT, MixedWideCrosspoint.point =         *)
(* C1092MWX_POINT, translate = C1092RC_INSIDE_TRANSLATE.  Tag C1092MPC_.     *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMOmissionCenter.ml";;
needs "n12/geometry/CP_C1092_InwardCenterDiagonal.ml";;
needs "n12/geometry/CP_C1092_MixedWideCrosspoint.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;

let c1092mpc_rr tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm);;
let c1092mpc_by conv tm th =
  let e = conv tm in
  if aconv (rhs (concl e)) (concl th) then EQ_MP (SYM e) th
  else failwith ("c1092mpc_by: " ^ string_of_term (rhs (concl e)));;

(* Lean: right_halfpoint *)
let c1092mpc_right_halfpoint () =
  let neighbor = c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS in
  MP (SPECL (c1092moc_own 10 @ [`&3`; `&36 / &25`; `&8 / &5`; `&3 / &2`]) OO_VERTICAL_SEGMENT)
    (end_itlist CONJ [c1092moc_right_far (); CONJUNCT2 (CONJUNCT2 neighbor);
       c1092mpc_rr `&36 / &25 < &8 / &5`; c1092mpc_rr `&36 / &25 <= &3 / &2`; c1092mpc_rr `&3 / &2 <= &8 / &5`]);;
let C1092MPC_RIGHT_HALFPOINT = c1092moc_close 10 "&3" "&3 / &2" (c1092mpc_right_halfpoint ());;

let c1092mpc_m4 () = c1092moc_seed 4 (`&33 / &20`, `&33 / &20`);;
let c1092mpc_m5 () = c1092moc_seed 5 (`&47 / &20`, `&33 / &20`);;
let c1092mpc_m6 () = c1092moc_seed 6 (`&47 / &20`, `&47 / &20`);;

(* Lean: bottom_crosspoint *)
let c1092mpc_bottom_crosspoint () =
  let inward = c1092moc_use C1092MPPE_OMITTED_BOTTOM_INWARD
  and neighbor = c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS in
  let t, eqs = c1092moc_layers 5 [C1092MOC_Y] in
  c1092moc_apply (c1092moc_conv eqs) (SPECL t C981CP_POINT)
    [c1092moc_punit 5 t; c1092moc_pos (); c1092moc_side ();
     CONJUNCT1 inward; CONJUNCT2 inward; c1092mpc_m5 ();
     c1092moc_excl 5 6 (c1092mpc_m6 ()); c1092moc_excl 5 4 (c1092mpc_m4 ());
     c1092moc_excl 5 10 (CONJUNCT2 (CONJUNCT2 neighbor));
     c1092moc_excl 5 10 (c1092mpc_right_halfpoint ())];;
let C1092MPC_BOTTOM_CROSSPOINT = c1092moc_close 5 "&2" "&3 / &2" (c1092mpc_bottom_crosspoint ());;

(* Lean: diagonal *)
let c1092mpc_diagonal () =
  let t, eqs = c1092moc_layers 5 [C1092MOC_Y; c1092moc_tr `&2` `&2`] in
  let conv = c1092moc_conv eqs in
  let facts = [c1092moc_punit 5 t; c1092moc_pos (); c1092moc_side ();
               c1092moc_bottom_center (); c1092mpc_m5 ();
               c1092moc_excl 5 4 (c1092mpc_m4 ()); c1092moc_excl 5 6 (c1092mpc_m6 ())] in
  CONJ (c1092moc_apply conv (SPECL t C1092ICD_POINT) facts)
       (c1092moc_apply conv (SPECL t C1092ICD_LONG_POINT) facts);;
let C1092MPC_DIAGONAL =
  prove(parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s /\\ %s"
          C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT
          (c1092mppe_in 5 "&5 / &2" "&3 / &2") (c1092mppe_in 5 "&261 / &100" "&139 / &100")),
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MOC_CODE_CONV THEN ACCEPT_TAC (c1092mpc_diagonal ()));;

(* Lean: right_crosspoint *)
let c1092mpc_right_crosspoint () =
  let inward = c1092moc_use C1092MPPE_OMITTED_BOTTOM_INWARD in
  let bbar = c1092moc_use C1092MPPE_OMITTED_BOTTOM_BAR in
  let tC, eqsC = c1092moc_layers 5 C1092MOC_CHART and tW, eqsW = c1092moc_layers 9 C1092MOC_CHART in
  let conv = c1092moc_conv (eqsC @ eqsW) in
  let win x y = list_mk_comb(`linside`, tW @ [x; y]) in
  let bar =
    let lo = `--(&39 / &100) <= y` and hi = `y <= &2 / &5` in
    let th = SPEC `y + &2` bbar in
    let bt = MP (MP th (c1092moc_arith [ASSUME lo] (lhand (concl th))))
                (c1092moc_arith [ASSUME hi] (lhand (rand (concl th)))) in
    GEN `y:real` (DISCH lo (DISCH hi (c1092mpc_by conv (win `&1` `y:real`) bt))) in
  let wallW =
    let lin = ASSUME (win `x:real` `y:real`) in
    let l0 = EQ_MP (c1092moc_unfold eqsW (concl lin)) lin in
    let args = snd (strip_comb (concl l0)) in
    let b = MP (SPECL [el 5 args; el 6 args] (REWRITE_RULE[lcont] (c1092moc_box 9))) l0 in
    GENL [`x:real`; `y:real`] (DISCH (concl lin) (c1092moc_arith [b] `x <= &2`)) in
  let cutW =
    let e = MP (SPECL (c1092moc_own 9) C1092MOC_CENTER_CHART) (c1092moc_unit 9) in
    let bc = MP (SPECL C1092MPPE_V C1092MOC_BOTTOM_CUT) (ASSUME C1092MOC_CTX) in
    c1092moc_arith [e; bc] (mk_binop `(<=):real->real->bool` (list_mk_comb(`lcy`, tW)) `&0`) in
  let disj =
    let tm = list_mk_comb(`ldisj`, tC @ tW) in
    let eq = (REWRITE_CONV[ldisj] THENC c1092moc_unfold (eqsC @ eqsW)) tm in
    EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real`
      (SPECL [`y + &2`; `&4 - (x + &2)`] (c1092moc_apart 5 9)))) in
  c1092moc_apply conv (SPECL (tC @ tW) C1092MWX_POINT)
    [c1092moc_punit 5 tC; c1092moc_punit 9 tW; c1092moc_pos (); c1092moc_side (); c1092moc_cap ();
     REFL `l:real`; c1092moc_bottom_center (); c1092mpc_m5 (); CONJUNCT2 inward; CONJUNCT1 inward;
     c1092moc_excl 5 6 (c1092mpc_m6 ()); c1092moc_excl 5 4 (c1092mpc_m4 ());
     c1092moc_seed 9 (`&2`, `&457 / &500`); bar;
     CONV_RULE C1092MOC_CODE_CONV (ASSUME C1092MOC_OMIT); wallW; cutW; disj];;
let C1092MPC_RIGHT_CROSSPOINT = c1092moc_close 5 "&5 / &2" "&2" (c1092mpc_right_crosspoint ());;

(* Lean: rectangle *)
let C1092MPC_RECTANGLE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> !x y. &2 <= x ==> x <= &5 / &2 ==> &3 / &2 <= y ==> y <= &2 ==> %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT (c1092mppe_in 5 "x" "y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&3 / &2`; `&2`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&2`; `&5 / &2`] THEN
  ASM_SIMP_TAC[C1092MPC_BOTTOM_CROSSPOINT; C1092MPC_DIAGONAL; C1092MOC_BOTTOM_CENTER;
               C1092MPC_RIGHT_CROSSPOINT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
