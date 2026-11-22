(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNorthwestActualSign.lean             *)
(* (N12Compact.C1092MPPMNorthwestActualSign).  The complete local northwest  *)
(* sign argument joined to the original one-omission owners.  Conventions   *)
(* and forward toolkit of CP_C1092_MPPMOmissionCenter.ml (c1092moc_          *)
(* functions; owners p i at mask EL i c1092wc_code, side l; WallContext p    *)
(* mppm is C1092MPPE_CTX, omitted is C1092MPPE_OMIT); the private side_gt /  *)
(* side_cap / side_same / marker_point are C1092MOC_SIDE_GT / SIDE_CAP /     *)
(* SIDE_SAME / MARKER_POINT.  PositiveActual p W is c1092mpnwas_pos (the     *)
(* OpenSquare invariants of W as explicit conjuncts of the existential).     *)
(* The V / profile / cut construction is that of C1092MTO right_origin       *)
(* (CP_C1092_MPPMTopOrigin.ml): B = C1092MOC_CHART of owner 9,               *)
(* MixedWideCrossing.centered_frame C1092MWC_CENTERED_FRAME, MixedWideWall.  *)
(* canonical_profile C1092MWW_CANONICAL_PROFILE, bCenter                     *)
(* C1092MOC_CENTER_CHART, (hb 1).1 C1092MOC_BOTTOM_CUT.  L = turnFrame       *)
(* (turnFrame (translate (pullX V) 4 0)).  MPPMUpperSign.exists_positive /   *)
(* faces C1092MPUS_EXISTS_POSITIVE / C1092MPUS_FACES; ClosedFrames.          *)
(* canonical_frame CLF_CANONICAL_FRAME; MPPMNorthwestSign.                   *)
(* nonpositive_impossible C1092MPNW_NONPOSITIVE_IMPOSSIBLE; bottom_center    *)
(* C1092MOC_BOTTOM_CENTER; MPPMPointCore.bottom_crosspoint / diagonal        *)
(* C1092MPC_BOTTOM_CROSSPOINT / C1092MPC_DIAGONAL.  Tag C1092MPNWAS_.        *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMNorthwestSign.ml";;
needs "n12/geometry/CP_C1092_MixedWideWall.ml";;
needs "n12/geometry/CP_C1092_MPPMTopOrigin.ml";;
needs "n12/geometry/CP_C1092_MPPMPointCore.ml";;

(* Lean: PositiveActual (structure; fields side, actual, normal, positive) *)
let c1092mpnwas_pos = new_definition
 `c1092mpnwas_pos c1 c2 a b l (cW:real) (sW:real) (uW:real) (vW:real) (aW:real) <=>
    aW = l /\
    (forall x y. linside cW sW uW vW aW x y <=>
           linside (ooc c1 c2 a b l (EL 5 c1092wc_code)) (oos c1 c2 a b l (EL 5 c1092wc_code))
                   (oou c1 c2 a b l (EL 5 c1092wc_code)) (oov c1 c2 a b l (EL 5 c1092wc_code)) l
                   (&2 + y) (&2 + x)) /\
    c977cc_normal cW sW /\
    &0 < sW`;;

(* the contradiction of the nonpositive branch, from the chosen N and W *)
let c1092mpnwas_contra () =
  let wv = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
  and nv = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] in
  let tq, eqq = c1092moc_layers 5 [C1092MOC_SW; c1092moc_tr `&2` `&2`] in
  let winside = ASSUME (list_mk_forall([`x:real`; `y:real`],
    mk_eq(list_mk_comb(`linside`, wv @ [`x:real`; `y:real`]),
          list_mk_comb(`linside`, tq @ [`x:real`; `y:real`])))) in
  let wu = ASSUME `cW * cW + sW * sW = &1` and wc = ASSUME `&0 < cW`
  and ws = ASSUME `abs sW <= cW` and wside = ASSUME `(aW:real) = l`
  and wsign = ASSUME `sW <= &0` in
  let npos = ASSUME (list_mk_comb(`c1092mpus_pos`, C1092MPPE_V @ nv)) in
  let [nunit; npos0; nside; ninside; nnormal; npositive] =
    CONJUNCTS (CONV_RULE C1092MOC_CODE_CONV (REWRITE_RULE[c1092mpus_pos; GSYM CONJ_ASSOC] npos)) in
  let nfaces = MP (SPECL (C1092MPPE_V @ nv) C1092MPUS_FACES)
    (end_itlist CONJ [ASSUME C1092MOC_NP; ASSUME C1092MOC_IMG; ASSUME C1092MOC_CTX;
                      ASSUME C1092MOC_OMIT; npos]) in
  let bbar = c1092moc_use C1092MPPE_OMITTED_BOTTOM_BAR in
  let rr tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm) in
  let bot x = let th = SPEC x bbar in MP (MP th (rr (lhand (concl th)))) (rr (lhand (rand (concl th)))) in
  let side = c1092moc_side () and cap = c1092moc_cap () and pos = c1092moc_pos () in
  let tB, eqsB = c1092moc_layers 9 C1092MOC_CHART in
  let ex = MP (SPECL tB C1092MWC_CENTERED_FRAME) (CONJ (c1092moc_punit 9 tB) pos) in
  let vv = [`cV:real`; `sV:real`; `uV:real`; `vV:real`; `aV:real`] in
  let body = let rec strip vs tm = match vs with [] -> tm | v :: r ->
      let bv, b = dest_exists tm in strip r (vsubst [v, bv] b) in strip vv (concl ex) in
  let [vu; vpos; vc; range; vside; vcenter; vinside] = CONJUNCTS (ASSUME body) in
  let convV = GEN_REWRITE_CONV ONCE_DEPTH_CONV [vinside] THENC c1092moc_conv eqsB in
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
  let m5 = c1092moc_seed 5 (`&47 / &20`, `&33 / &20`)
  and m4 = c1092moc_seed 4 (`&33 / &20`, `&33 / &20`)
  and m6 = c1092moc_seed 6 (`&47 / &20`, `&47 / &20`) in
  let profile = c1092moc_apply2 ALL_CONV (SPECL vv C1092MWW_CANONICAL_PROFILE)
    [vu; vpos; sideV; capV; vc; range; wallV; cutV;
     c1092mto_by convV (vin `&543 / &500` `&0`) (c1092moc_seed 9 (`&2`, `&457 / &500`));
     c1092mto_by convV (vin `&1` `--(&39 / &100)`) (bot `&161 / &100`);
     c1092mto_by convV (vin `&1` `&2 / &5`) (bot `&12 / &5`);
     c1092mto_by convV (mk_neg (vin `&1` `--(&2 / &5)`)) omitted;
     c1092mto_by convV (mk_neg (vin `&7 / &20` `&7 / &20`)) (c1092moc_excl 9 5 m5)] [] in
  let [p1; p2; p3; _; _; _] = CONJUNCTS profile in
  let tL, eqsL = c1092moc_layers_of vv [C1092MOC_X; c1092moc_tr `&4` `&0`; C1092MTO_TURN; C1092MTO_TURN] in
  let convL = c1092moc_unfold eqsL THENC convV in
  let normalL =
    let tm = list_mk_comb(`c977cc_normal`, [el 0 tL; el 1 tL]) in
    MP (prove(mk_imp(list_mk_conj [concl vu; concl p1; concl p2], tm),
              REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_NEG; REAL_NEG_MUL2] THEN
              STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC))
       (end_itlist CONJ [vu; p1; p2]) in
  let sumL = c1092moc_arith [p3]
    (mk_binop `(<):real->real->bool` `&5 / &4` (mk_binop `(+):real->real->real` (el 0 tL) (el 1 tL))) in
  let centerL =
    let tm = mk_binop `(<=):real->real->bool` (list_mk_comb(`lcy`, tL)) `&0` in
    MP (prove(mk_imp(concl cutV, tm), REWRITE_TAC[lcy] THEN REAL_ARITH_TAC)) cutV in
  let dn =
    MP (prove(mk_imp(list_mk_conj [concl wu; concl ws; concl wsign], `c977cc_normal cW (--sW)`),
              REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
              UNDISCH_TAC `abs sW <= cW` THEN UNDISCH_TAC `sW <= &0` THEN
              UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
              REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC))
       (end_itlist CONJ [wu; ws; wsign]) in
  let convW = GEN_REWRITE_CONV ONCE_DEPTH_CONV [winside] THENC c1092moc_conv eqq in
  let convN = GEN_REWRITE_CONV ONCE_DEPTH_CONV [ninside] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let convAll = TRY_CONV convW THENC TRY_CONV convN THENC TRY_CONV convL THENC
                ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let norm = [REAL_ADD_RID; REAL_ARITH `forall x. &4 - (&4 - (x + &4) + &2) = x + &2`;
              REAL_ARITH `forall y. &2 + y = y + &2`] in
  let disj conv apart tm =
    let eq = (REWRITE_CONV[ldisj] THENC conv) tm in
    let r = rhs (concl eq) in
    EQ_MP (SYM eq) (MP (prove(mk_imp(concl apart, r),
      DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC norm THEN ASM_REWRITE_TAC[])) apart) in
  let disjWN = disj (TRY_CONV convW THENC TRY_CONV convN) (c1092moc_apart 5 6) (list_mk_comb(`ldisj`, wv @ nv)) in
  let disjWL = disj (TRY_CONV convW THENC TRY_CONV convL) (c1092moc_apart 5 9) (list_mk_comb(`ldisj`, wv @ tL)) in
  let neighbors = c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS in
  let f = c1092moc_apply2 convAll (SPECL (wv @ nv @ tL) C1092MPNW_NONPOSITIVE_IMPOSSIBLE)
    [wu; nunit; c1092moc_unit_of vu tL; dn; nnormal; npositive; nfaces;
     c1092moc_use C1092MOC_BOTTOM_CENTER; c1092moc_use C1092MPC_BOTTOM_CROSSPOINT;
     CONJUNCT1 (c1092moc_use C1092MPC_DIAGONAL); m5;
     c1092moc_excl 5 4 m4; c1092moc_excl 5 6 m6;
     m6; CONJUNCT2 (CONJUNCT1 neighbors);
     normalL; sumL; centerL;
     bot `&12 / &5`; bot `&47 / &20`; bot `&161 / &100`;
     disjWN; disjWL]
    [wside; nside; vside; side] in
  c1092moc_choose vv ex f;;

(* Lean: exists_positive *)
let C1092MPNWAS_EXISTS_POSITIVE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> ?cW sW uW vW aW. cW * cW + sW * sW = &1 /\\ &0 < aW /\\
      c1092mpnwas_pos %s cW sW uW vW aW" C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPUS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cN:real` (X_CHOOSE_THEN `sN:real` (X_CHOOSE_THEN `uN:real`
    (X_CHOOSE_THEN `vN:real` (X_CHOOSE_THEN `aN:real` ASSUME_TAC))))) THEN
  let tq, eqq = c1092moc_layers 5 [C1092MOC_SW; c1092moc_tr `&2` `&2`] in
  MP_TAC(MP (SPECL tq CLF_CANONICAL_FRAME) (CONJ (c1092moc_punit 5 tq) (c1092moc_pos ()))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cW:real` (X_CHOOSE_THEN `sW:real` (X_CHOOSE_THEN `uW:real`
    (X_CHOOSE_THEN `vW:real` (X_CHOOSE_THEN `aW:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `&0 < sW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN ACCEPT_TAC (c1092mpnwas_contra ());
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  REWRITE_TAC[c1092mpnwas_pos] THEN CONV_TAC C1092MOC_CODE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV (c1092moc_conv eqq)) THEN
    REWRITE_TAC[REAL_ARITH `forall y. y + &2 = &2 + y`];
    REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
    MAP_EVERY UNDISCH_TAC [`abs sW <= cW`; `&0 < sW`; `cW * cW + sW * sW = &1`] THEN
    REAL_ARITH_TAC]);;
