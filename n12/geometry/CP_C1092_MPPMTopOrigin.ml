(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMTopOrigin.lean                       *)
(* (namespace N12Compact.C1092MPPMTopOrigin).  The mixed-wall/corner         *)
(* obstruction forces the right wall point (3,2) in its actual owner under   *)
(* the bottom omission.  Conventions and forward toolkit of                  *)
(* CP_C1092_MPPMOmissionCenter.ml (the c1092moc_ functions): owners p i at mask           *)
(* EL i c1092wc_code (1 -> 12, 5 -> 512, 9 -> 8192, 10 -> 16384).  The       *)
(* private chart / inside_chart / center_chart are C1092MOC_CHART /          *)
(* C1092MOC_INSIDE_CHART / C1092MOC_CENTER_CHART, side_gt / side_cap /       *)
(* side_same / marker_point are C1092MOC_SIDE_GT / SIDE_CAP / SIDE_SAME /    *)
(* MARKER_POINT.  turnFrame (c,s,u,v,a) = (--s, c, v, --u - a, a)            *)
(* (C1092MTO_TURN_INSIDE).  MixedWideCrossing.centered_frame =               *)
(* C1092MWC_CENTERED_FRAME, MixedWideWall.canonical_profile =                *)
(* C1092MWW_CANONICAL_PROFILE, MixedCornerObstruction.impossible =           *)
(* C1092MCO_IMPOSSIBLE, C981CompletionTopReach.origin_alternative =          *)
(* C981TR_ORIGIN_ALTERNATIVE, boundary_origin = OCWPBO_BOUNDARY_ORIGIN.      *)
(* Tag C1092MTO_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMOmissionCenter.ml";;
needs "n12/geometry/CP_C1092_MixedCornerObstruction.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/CP_C981_TopReach.ml";;

(* S12.turnFrame_inside *)
let C1092MTO_TURN_INSIDE = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C1092MTO_TURN = (C1092MTO_TURN_INSIDE, ([]:term list));;

let C1092MTO_BOX_Y = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;
let C1092MTO_BOX_XY = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;

(* a fact about a layered tuple from the owner fact, through conv *)
let c1092mto_by conv tm th =
  let e = conv tm in
  if aconv (rhs (concl e)) (concl th) then EQ_MP (SYM e) th
  else failwith ("c1092mto_by: " ^ string_of_term (rhs (concl e)));;

(* the box bound !x y. linside T x y ==> bound, from the owner's container *)
let c1092mto_box i conv t bound =
  let lin = ASSUME (list_mk_comb(`linside`, t @ [`x:real`; `y:real`])) in
  let l0 = EQ_MP (conv (concl lin)) lin in
  let args = snd (strip_comb (concl l0)) in
  let b = MP (SPECL [el 5 args; el 6 args] (REWRITE_RULE[lcont] (c1092moc_box i))) l0 in
  GENL [`x:real`; `y:real`] (DISCH (concl lin) (c1092moc_arith [b] bound));;

(* Lean: corner_halfpoint (private) *)
let c1092mto_corner_halfpoint missing =
  let neighbor = c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS in
  let goal = list_mk_comb(`linside`, c1092moc_own 1 @ [`&5 / &2`; `&1`]) in
  let absent = ASSUME (mk_neg goal) in
  let layers = [C1092MOC_X; C1092MOC_SW] in
  let tB, eqB = c1092moc_layers 10 layers and tK, eqK = c1092moc_layers 1 layers in
  let disj =
    let tm = list_mk_comb(`ldisj`, tK @ tB) in
    let eq = (REWRITE_CONV[ldisj] THENC c1092moc_unfold (eqK @ eqB)) tm in
    EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real` (SPECL [`&4 - y`; `x:real`] (c1092moc_apart 1 10)))) in
  let h = c1092moc_apply (c1092moc_conv (eqB @ eqK))
    (SPECL (tB @ tK @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN)
    [c1092moc_punit 10 tB; c1092moc_punit 1 tK; c1092moc_pos (); c1092moc_side (); REFL `l:real`;
     MATCH_MP C1092MTO_BOX_Y (c1092moc_plcont 10 layers); MATCH_MP C1092MTO_BOX_XY (c1092moc_plcont 1 layers);
     c1092moc_seed 10 (`&1543 / &500`, `&2`); CONJUNCT2 (CONJUNCT2 neighbor);
     c1092moc_seed 1 (`&1543 / &500`, `&1`); c1092moc_seed 1 (`&3`, `&1`); absent; disj] in
  CCONTR goal (MP (NOT_ELIM missing) h);;

(* Lean: right_alternative (private) *)
let c1092mto_right_alternative missing =
  let neighbor = c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS in
  let t, eqs = c1092moc_layers 10 [C1092MOC_Y; C1092MOC_SW; c1092moc_tr `&2` `&3`] in
  let conv = c1092moc_conv eqs in
  c1092moc_apply conv (SPECL t C981TR_ORIGIN_ALTERNATIVE)
    [c1092moc_punit 10 t; c1092moc_pos (); c1092moc_side ();
     c1092mto_box 10 (c1092moc_unfold eqs) t `y <= &1`;
     c1092moc_seed 10 (`&1543 / &500`, `&2`); CONJUNCT2 (CONJUNCT2 neighbor); missing];;

let C1092MTO_MISSING = mk_neg (list_mk_comb(`linside`, c1092moc_own 10 @ [`&3`; `&2`]));;

(* Lean: right_origin *)
let c1092mto_right_origin () =
  let goal = rand C1092MTO_MISSING in
  let missing = ASSUME C1092MTO_MISSING in
  let half = c1092mto_corner_halfpoint missing in
  let alternative = c1092mto_right_alternative missing in
  let bbar = c1092moc_use C1092MPPE_OMITTED_BOTTOM_BAR in
  let rr tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm) in
  let bot x = let th = SPEC x bbar in MP (MP th (rr (lhand (concl th)))) (rr (lhand (rand (concl th)))) in
  let side = c1092moc_side () and cap = c1092moc_cap () and pos = c1092moc_pos () in
  let tW, eqsW = c1092moc_layers 9 C1092MOC_CHART in
  let ex = MP (SPECL tW C1092MWC_CENTERED_FRAME) (CONJ (c1092moc_punit 9 tW) pos) in
  let vv = [`cV:real`; `sV:real`; `uV:real`; `vV:real`; `aV:real`] in
  let body = let rec strip vs tm = match vs with [] -> tm | v :: r ->
      let bv, b = dest_exists tm in strip r (vsubst [v, bv] b) in strip vv (concl ex) in
  let [vu; vpos; vc; range; vside; vcenter; vinside] = CONJUNCTS (ASSUME body) in
  let convV = GEN_REWRITE_CONV ONCE_DEPTH_CONV [vinside] THENC c1092moc_conv eqsW in
  let vin x y = list_mk_comb(`linside`, vv @ [x; y]) in
  let sideV = c1092moc_arith [vside; side] `&1 < aV` in
  let capV = c1092moc_arith [vside; cap] `aV <= &1001 / &1000` in
  let wallV =
    let lin = ASSUME (vin `x:real` `y:real`) in
    let l0 = EQ_MP (convV (concl lin)) lin in
    let args = snd (strip_comb (concl l0)) in
    let b = MP (SPECL [el 5 args; el 6 args] (REWRITE_RULE[lcont] (c1092moc_box 9))) l0 in
    GENL [`x:real`; `y:real`] (DISCH (concl lin) (c1092moc_arith [b] `x <= &2`)) in
  let cutV =
    let e = MP (SPECL (c1092moc_own 9) C1092MOC_CENTER_CHART) (c1092moc_unit 9) in
    let bc = MP (SPECL C1092MPPE_V C1092MOC_BOTTOM_CUT) (ASSUME C1092MOC_CTX) in
    c1092moc_arith [vcenter; e; bc] `lcy cV sV uV vV aV <= &0` in
  let omitted = CONV_RULE C1092MOC_CODE_CONV (ASSUME C1092MOC_OMIT) in
  let profile = c1092moc_apply2 ALL_CONV (SPECL vv C1092MWW_CANONICAL_PROFILE)
    [vu; vpos; sideV; capV; vc; range; wallV; cutV;
     c1092mto_by convV (vin `&543 / &500` `&0`) (c1092moc_seed 9 (`&2`, `&457 / &500`));
     c1092mto_by convV (vin `&1` `--(&39 / &100)`) (bot `&161 / &100`);
     c1092mto_by convV (vin `&1` `&2 / &5`) (bot `&12 / &5`);
     c1092mto_by convV (mk_neg (vin `&1` `--(&2 / &5)`)) omitted;
     c1092mto_by convV (mk_neg (vin `&7 / &20` `&7 / &20`))
       (c1092moc_excl 9 5 (c1092moc_seed 5 (`&47 / &20`, `&33 / &20`)))] [] in
  let [p1; p2; _; _; p5; _] = CONJUNCTS profile in
  let tL, eqsL = c1092moc_layers_of vv [C1092MOC_X; C1092MTO_TURN; C1092MTO_TURN; c1092moc_tr `&3` `&0`] in
  let tK, eqsK = c1092moc_layers 1 [C1092MOC_SW; c1092moc_tr `&1` `&2`] in
  let convLK = c1092moc_unfold (eqsL @ eqsK) THENC convV in
  let lin x y = list_mk_comb(`linside`, tL @ [x; y]) and kin x y = list_mk_comb(`linside`, tK @ [x; y]) in
  let normalL =
    let tm = list_mk_comb(`c977cc_normal`, [el 0 tL; el 1 tL]) in
    MP (prove(mk_imp(list_mk_conj [concl vu; concl p1; concl p2], tm),
              REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_NEG; REAL_NEG_MUL2] THEN
              STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC))
       (end_itlist CONJ [vu; p1; p2]) in
  let sineL = c1092moc_arith [p1] (mk_binop `(<):real->real->bool` `&0` (el 1 tL)) in
  let faceL = c1092moc_arith [p5]
    (mk_binop `(<=):real->real->bool` (mk_binop `( * ):real->real->real` `--(&2 / &5)` (el 0 tL)) (el 3 tL)) in
  let disj =
    let tm = list_mk_comb(`ldisj`, tL @ tK) in
    let eq = (REWRITE_CONV[ldisj] THENC convLK THENC
              REWRITE_CONV[REAL_ARITH `forall y. (y + &0) + &2 = y + &2`;
                           REAL_ARITH `forall x. &4 - ((&4 - (x + &3)) + &2) = x + &1`]) tm in
    EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real` (SPECL [`y + &2`; `x + &1`] (c1092moc_apart 9 1)))) in
  let f = c1092moc_apply2 (convLK THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (SPECL (tL @ tK) C1092MCO_IMPOSSIBLE)
    [c1092moc_unit_of vu tL; vpos; c1092moc_punit 1 tK; pos; sideV; normalL; sineL; faceL;
     c1092mto_by (convLK THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (lin `&0` `&2 / &5`) (bot `&12 / &5`);
     half; c1092moc_seed 1 (`&3`, `&1`); c1092moc_excl 1 10 alternative; disj] [vside] in
  CCONTR goal (c1092moc_choose vv ex f);;
let C1092MTO_RIGHT_ORIGIN = c1092moc_close 10 "&3" "&2" (c1092mto_right_origin ());;

(* Lean: right_segment *)
let C1092MTO_RIGHT_SEGMENT = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> !y. &36 / &25 <= y ==> y <= &2 ==> %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT (c1092mppe_in 10 "&3" "y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&2`] THEN
  ASM_SIMP_TAC[C1092MOC_RIGHT_FAR; C1092MTO_RIGHT_ORIGIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
