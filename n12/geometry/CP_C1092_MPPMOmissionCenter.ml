(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOmissionCenter.lean                  *)
(* (namespace N12Compact.C1092MPPMOmissionCenter).  An actual omitted MPPM   *)
(* wall auxiliary forces the strict central origin in its inward owner.      *)
(* Conventions of CP_C1092_MPPMEntrance.ml: owners p i is the owner 5-tuple  *)
(* at mask EL i c1092wc_code (5 -> 512, 6 -> 1024, 9 -> 8192, 10 -> 16384;   *)
(* side l); WallContext p mppm is c1092wc_ctx c1 c2 a b l c1092mppe_mppm;    *)
(* omitted is ~(owners p 9).Inside (8/5) 1.  pullX / pullY / pullSwap are    *)
(* LINSIDE_PULLX / PULLY / PULLSW, RigidCharts translate / swap are          *)
(* C1092RC_INSIDE_TRANSLATE / C1092RC_INSIDE_SWAP (tuples), chart q =        *)
(* translate (pullSwap (pullY q)) 2 2.  ClosedFrames.canonical_frame =       *)
(* CLF_CANONICAL_FRAME, InwardBarCenter.point = C1092IBC_POINT,              *)
(* InwardMissingProfile.profile = C1092IMP_PROFILE (Profile =                *)
(* C1092IMP_profile), MixedWideCrossing.point = C1092MWC_POINT,              *)
(* InwardCrossingConflict.impossible = C1092ICC_IMPOSSIBLE,                  *)
(* WallLowerReach.point = WLR_POINT, C1092WallProfileScalars.half =          *)
(* C1092WPS_half (identities C1092IBC_HALF).  Tag C1092MOC_.                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMEntrance.ml";;
needs "n12/geometry/CP_C1092_InwardBarCenter.ml";;
needs "n12/geometry/CP_C1092_InwardMissingProfile.ml";;
needs "n12/geometry/CP_C1092_MixedWideCrossing.ml";;
needs "n12/geometry/CP_C1092_InwardCrossingConflict.ml";;
needs "n12/geometry/CP_C1092_RigidCharts.ml";;
needs "n12/geometry/WallLowerReach.ml";;

(* Lean: side_gt (private) *)
let C1092MOC_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`, REWRITE_TAC[OO_SIDE]);;
(* Lean: side_cap (private) *)
let C1092MOC_SIDE_CAP = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> l <= &1001 / &1000`, REWRITE_TAC[OO_SIDE_LE]);;
(* Lean: side_same (private) *)
let C1092MOC_SIDE_SAME = prove (`forall l:real. l = l`, REWRITE_TAC[]);;
(* Lean: marker_point (private) *)
let C1092MOC_MARKER_POINT = prove
 (parse_term (Printf.sprintf "!%s i j. %s /\\ i < 12 /\\ j < 16 /\\ j IN bitset (EL i c1092wc_code) ==> linside %s (marker j$1) (marker j$2)"
    C1092AE_P C1092AE_HYP
    "(ooc c1 c2 a b l (EL i c1092wc_code)) (oos c1 c2 a b l (EL i c1092wc_code)) (oou c1 c2 a b l (EL i c1092wc_code)) (oov c1 c2 a b l (EL i c1092wc_code)) l"),
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`i:num`]) C1092WC_OWNERS_MARKERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]);;

(* ---- forward toolkit (literal masks; hyps NPACK, IMAGE, ctx, omitted) ---- *)
let C1092MOC_NP = `NPACK c1 c2 a b l`;;
let C1092MOC_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`;;
let C1092MOC_CTX = parse_term C1092MPPE_CTX;;
let C1092MOC_OMIT = parse_term C1092MPPE_OMIT;;
let C1092MOC_CODE_CONV = REWRITE_CONV (Array.to_list C1092WC_CODE_EL);;
let C1092MOC_MASKS = [3;12;48;192;256;512;1024;2048;4096;8192;16384;32768];;
let c1092moc_own i =
  map (fun f -> list_mk_comb(f, C1092MPPE_V @ [mk_small_numeral (el i C1092MOC_MASKS)]))
    [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c1092moc_hh () = CONJ (ASSUME C1092MOC_NP) (ASSUME C1092MOC_IMG);;
(* use an EL-form packing theorem; its hypothesis is a conjunction of NPACK, IMAGE, ctx, omitted *)
let c1092moc_use th =
  let th1 = SPECL C1092MPPE_V th in
  let hs = [C1092MOC_NP; C1092MOC_IMG; C1092MOC_CTX; C1092MOC_OMIT] in
  let rec build tm = if mem tm hs then ASSUME tm else
    let l, r = dest_conj tm in CONJ (build l) (build r) in
  CONV_RULE C1092MOC_CODE_CONV (MP th1 (build (lhand (concl th1))));;
let c1092moc_side () = MP (SPECL C1092MPPE_V OO_SIDE) (ASSUME C1092MOC_NP);;
let c1092moc_cap () = MP (SPECL C1092MPPE_V OO_SIDE_LE) (ASSUME C1092MOC_NP);;
let c1092moc_pos () = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) (c1092moc_side ());;
let c1092moc_unit i = MP (SPECL (C1092MPPE_V @ [mk_small_numeral (el i C1092MOC_MASKS)]) OO_UNIT) (ASSUME C1092MOC_NP);;
let c1092moc_box i = MP (SPECL (C1092MPPE_V @ [mk_small_numeral (el i C1092MOC_MASKS)]) OO_BOX) (ASSUME C1092MOC_NP);;
let c1092moc_seed i (x, y) =
  MP (SPECL C1092MPPE_V (oo_inst `c1092wc_family` (oo_seed (el i C1092MOC_MASKS) (x, y)))) (c1092moc_hh ());;
let c1092moc_apart i j =
  REWRITE_RULE[ldisj] (MP (SPECL C1092MPPE_V
    (oo_apart `c1092wc_family` (el i C1092MOC_MASKS) (el j C1092MOC_MASKS))) (c1092moc_hh ()));;
let c1092moc_excl i j pt =
  let args = snd (strip_comb (concl pt)) in
  let d2 = SPECL [el 5 args; el 6 args] (c1092moc_apart i j) in
  let a = lhand (rand (concl d2)) in
  NOT_INTRO (DISCH a (MP (NOT_ELIM d2) (CONJ (ASSUME a) pt)));;

(* layered tuples: (lemma, extra args), innermost first *)
let C1092MOC_X = (LINSIDE_PULLX, ([]:term list)) and C1092MOC_Y = (LINSIDE_PULLY, ([]:term list))
and C1092MOC_SW = (LINSIDE_PULLSW, ([]:term list));;
let c1092moc_tr dx dy = (C1092RC_INSIDE_TRANSLATE, [dx; dy]);;
let C1092MOC_SWAP = (C1092RC_INSIDE_SWAP, ([]:term list));;
let c1092moc_layers_of base layers =
  let step (cur, eqs) (pth, extra) =
    let t = SPECL (cur @ extra @ [`x:real`; `y:real`]) pth in
    let args = snd (strip_comb (lhs (concl t))) in
    ([el 0 args; el 1 args; el 2 args; el 3 args; el 4 args], GENL [`x:real`; `y:real`] t :: eqs) in
  rev_itlist (fun l acc -> step acc l) layers (base, []);;
let c1092moc_layers i layers = c1092moc_layers_of (c1092moc_own i) layers;;
(* rewrite with  |- !x y. linside T x y <=> ..  only at the exact tuple T *)
let c1092moc_exact e =
  let _, b = strip_forall (concl e) in
  let tup = fst (chop_list 5 (snd (strip_comb (lhs b)))) in
  fun tm ->
    let f, args = strip_comb tm in
    if not (is_const f && fst (dest_const f) = "linside") || length args <> 7 then failwith "exact" else
    let t5, xy = chop_list 5 args in
    if forall2 aconv t5 tup then SPECL xy e else failwith "exact";;
let c1092moc_unfold eqs = EVERY_CONV (map (fun e -> ONCE_DEPTH_CONV (c1092moc_exact e)) eqs);;
let c1092moc_conv eqs = c1092moc_unfold eqs THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;
let c1092moc_unit_of uth t =
  let c = el 0 t and s = el 1 t in
  let tm = mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                   (mk_binop `( * ):real->real->real` s s), `&1`) in
  MP (prove(mk_imp(concl uth, tm), CONV_TAC REAL_RING)) uth;;
let c1092moc_punit i t = c1092moc_unit_of (c1092moc_unit i) t;;
let c1092moc_plcont i layers =
  itlist (fun (pth, _) acc ->
    MATCH_MP (if pth == LINSIDE_PULLX then LCONT_PULLX else if pth == LINSIDE_PULLY then LCONT_PULLY
              else LCONT_PULLSW) acc) (rev layers) (c1092moc_box i);;

(* discharge the antecedents of spec from facts, up to conv *)
let c1092moc_apply conv spec facts =
  let ants = conjuncts (lhand (concl spec)) in
  let pa tm =
    try find (fun f -> aconv (concl f) tm) facts with Failure _ ->
    let eq = conv tm in
    let r = rhs (concl eq) in
    if r = `true` then EQT_ELIM eq else
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) r) facts)
    with Failure _ -> failwith ("c1092moc_apply: " ^ string_of_term tm) in
  CONV_RULE conv (MP spec (end_itlist CONJ (map pa ants)));;
(* linear arithmetic consequence of facts *)
let c1092moc_arith hs tm =
  MP (REAL_ARITH (mk_imp(list_mk_conj (map concl hs), tm))) (end_itlist CONJ hs);;

let c1092moc_stmt i x y = parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s"
  C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT (c1092mppe_in i x y));;
let c1092moc_close i x y th =
  prove(c1092moc_stmt i x y,
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MOC_CODE_CONV THEN ACCEPT_TAC th);;

(* Lean: right_far *)
let c1092moc_right_far () =
  let inward = c1092moc_use C1092MPPE_OMITTED_BOTTOM_INWARD
  and neighbor = c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS in
  let layers = [C1092MOC_X; C1092MOC_Y] in
  let t, eqs = c1092moc_layers 10 layers in
  c1092moc_apply (c1092moc_conv eqs) (SPECL t WLR_POINT)
    [c1092moc_punit 10 t; c1092moc_side (); c1092moc_plcont 10 layers;
     c1092moc_seed 10 (`&1543 / &500`, `&2`); CONJUNCT2 (CONJUNCT2 neighbor);
     c1092moc_excl 10 6 (CONJUNCT1 (CONJUNCT1 neighbor));
     c1092moc_excl 10 5 (CONJUNCT2 inward)];;
let C1092MOC_RIGHT_FAR = c1092moc_close 10 "&3" "&36 / &25" (c1092moc_right_far ());;

(* (hb 1).1: the bottom wall owner's center is left of x = 2 *)
let C1092MOC_BOTTOM_CUT = prove
 (`forall c1 c2 a b l. c1092wc_ctx c1 c2 a b l c1092mppe_mppm
     ==> lcx (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192)
             (oov c1 c2 a b l 8192) l <= &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092wc_ctx] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[c1092mppe_mppm; ARITH] THEN
  REWRITE_TAC[c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv;
              c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS @ Array.to_list C1092WC_CODE_EL) THEN
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* the chart translate (pullSwap (pullY q)) 2 2 *)
let C1092MOC_CHART = [C1092MOC_Y; C1092MOC_SW; c1092moc_tr `&2` `&2`];;

(* Lean: inside_chart (private) *)
let C1092MOC_INSIDE_CHART =
  let q = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] in
  let t, eqs = c1092moc_layers_of q C1092MOC_CHART in
  let tm = list_mk_comb(`linside`, t @ [`x:real`; `y:real`]) in
  prove(list_mk_forall(q @ [`x:real`; `y:real`],
          mk_eq(tm, list_mk_comb(`linside`, q @ [`&2 + y`; `&2 - x`]))),
    REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV (c1092moc_unfold eqs)) THEN
    REWRITE_TAC[REAL_ARITH `y + &2 = &2 + y /\ &4 - (x + &2) = &2 - x`]);;

(* Lean: center_chart (private) *)
let C1092MOC_CENTER_CHART =
  let q = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] in
  let t, _ = c1092moc_layers_of q C1092MOC_CHART in
  prove(list_mk_forall(q, mk_imp(`c * c + s * s = &1`,
          mk_eq(list_mk_comb(`lcy`, t), `lcx c s u v a - &2`))),
    REPEAT GEN_TAC THEN REWRITE_TAC[lcx; lcy] THEN CONV_TAC REAL_RING);;

(* discharge antecedents from facts / conv / linear or ring arithmetic over ahs *)
let c1092moc_apply2 conv spec facts ahs =
  let ants = conjuncts (lhand (concl spec)) in
  let pa tm =
    try find (fun f -> aconv (concl f) tm) facts with Failure _ ->
    let eq = conv tm in
    let r = rhs (concl eq) in
    if r = `true` then EQT_ELIM eq else
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) r) facts) with Failure _ ->
    try c1092moc_arith ahs tm with Failure _ ->
    try MP (prove(mk_imp(list_mk_conj (map concl ahs), tm), STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
                  FIRST_ASSUM(fun th -> MP_TAC th THEN CONV_TAC REAL_RING) ORELSE CONV_TAC REAL_RING))
           (end_itlist CONJ ahs)
    with Failure _ -> failwith ("c1092moc_apply2: " ^ string_of_term tm) in
  CONV_RULE conv (MP spec (end_itlist CONJ (map pa ants)));;

let rec c1092moc_choose vars ex th =
  match vars with
    [] -> PROVE_HYP ex th
  | v :: vs ->
      let bv, b = dest_exists (concl ex) in
      CHOOSE (v, ex) (c1092moc_choose vs (ASSUME (vsubst [v, bv] b)) th);;

(* Lean: bottom_center *)
let c1092moc_bottom_center () =
  let inward = c1092moc_use C1092MPPE_OMITTED_BOTTOM_INWARD
  and neighbor = c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS
  and bbar = c1092moc_use C1092MPPE_OMITTED_BOTTOM_BAR in
  let rr tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm) in
  let bot x = let th = SPEC x bbar in MP (MP th (rr (lhand (concl th)))) (rr (lhand (rand (concl th)))) in
  let m5 = c1092moc_seed 5 (`&47 / &20`, `&33 / &20`)
  and m6 = c1092moc_seed 6 (`&47 / &20`, `&47 / &20`)
  and m9 = c1092moc_seed 9 (`&2`, `&457 / &500`) in
  let side = c1092moc_side () and cap = c1092moc_cap () and pos = c1092moc_pos () in
  let t5, eqs5 = c1092moc_layers 5 C1092MOC_CHART in
  let ex = MP (SPECL t5 CLF_CANONICAL_FRAME) (CONJ (c1092moc_punit 5 t5) pos) in
  let cv = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] in
  let body = itlist (fun v tm -> let bv, b = dest_exists tm in vsubst [v, bv] b) (rev cv) (concl ex) in
  let body = let rec strip vs tm = match vs with [] -> tm | v :: r ->
      let bv, b = dest_exists tm in strip r (vsubst [v, bv] b) in strip cv (concl ex) in
  let [cu; apos; cp; range; shape; act; _] = CONJUNCTS (ASSUME body) in
  let convC = GEN_REWRITE_CONV ONCE_DEPTH_CONV [act] THENC c1092moc_conv eqs5 in
  let cin x y = list_mk_comb(`linside`, cv @ [x; y]) in
  let cfact tm th =
    let e = convC tm in
    if aconv (rhs (concl e)) (concl th) then EQ_MP (SYM e) th
    else failwith ("cfact: " ^ string_of_term (rhs (concl e))) in
  let sideC = c1092moc_arith [shape; side] `&1 < aC` in
  let capC = c1092moc_arith [shape; cap] `aC <= &1001 / &1000` in
  let m = cfact (cin `&7 / &20` `&7 / &20`) m5 in
  let p = cfact (cin `&0` `&13 / &50`) (CONJUNCT2 inward) in
  let q = cfact (cin `&13 / &50` `&0`) (CONJUNCT1 inward) in
  let missingA = cfact (mk_neg (cin `&2 / &5` `&1`)) (c1092moc_excl 5 10 (CONJUNCT2 (CONJUNCT2 neighbor))) in
  let missingN = cfact (mk_neg (cin `--(&7 / &20)` `&7 / &20`)) (c1092moc_excl 5 6 m6) in
  let missingR = cfact (mk_neg (cin `&1` `&2 / &5`)) (c1092moc_excl 5 9 (bot `&12 / &5`)) in
  let center =
    let pos_branch =
      let sgn = ASSUME `&0 <= sC` in
      let rf = c1092moc_right_far () in
      let n14 = cfact (mk_neg (cin `&14 / &25` `&1`)) (c1092moc_excl 5 10 rf) in
      let hy = `&0 <= y /\ y <= &39 / &100` in
      let bt = let th = SPEC `y + &2` bbar in
        MP (MP th (c1092moc_arith [ASSUME hy] (lhand (concl th))))
           (c1092moc_arith [ASSUME hy] (lhand (rand (concl th)))) in
      let bar = GEN `y:real` (DISCH hy (cfact (mk_neg (cin `&1` `y:real`)) (c1092moc_excl 5 9 bt))) in
      c1092moc_apply2 ALL_CONV (SPECL cv C1092IBC_POINT)
        [cu; apos; sideC; cp; sgn; m; p; q; missingA; n14; bar] [range; cp; sgn] in
    let neg_branch =
      let sgn = ASSUME `~(&0 <= sC)` in
      let missing = ASSUME (mk_neg (cin `&0` `&0`)) in
      let prof = c1092moc_apply2 ALL_CONV (SPECL cv C1092IMP_PROFILE)
        [cu; apos; sideC; cp; m; p; q; missing; missingR; missingA; missingN] [range; cp; sgn] in
      let [sine; lowerV; lowerU; _; _; outer; halfSmall] = CONJUNCTS (REWRITE_RULE[C1092IMP_profile] prof) in
      let z = `C1092WPS_half cC (--sC)` in
      let half = MP (SPECL [`cC:real`; `--sC`] C1092IBC_HALF)
        (end_itlist CONJ [c1092moc_arith [cp] `&0 <= cC`; c1092moc_arith [sine] `&0 <= --sC`;
                          c1092moc_unit_of cu [`cC:real`; `--sC`]]) in
      let [zp; _; angle; unitAngle] = CONJUNCTS half in
      let tW, eqsW = c1092moc_layers 9 C1092MOC_CHART in
      let convW = c1092moc_conv eqsW in
      let wfact tm th =
        let e = convW tm in
        if aconv (rhs (concl e)) (concl th) then EQ_MP (SYM e) th
        else failwith ("wfact: " ^ string_of_term (rhs (concl e))) in
      let win x y = list_mk_comb(`linside`, tW @ [x; y]) in
      let wallW =
        let lin = ASSUME (win `x:real` `y:real`) in
        let l9 = EQ_MP (convW (concl lin)) lin in
        let args = snd (strip_comb (concl l9)) in
        let b = MP (SPECL [el 5 args; el 6 args] (REWRITE_RULE[lcont] (c1092moc_box 9))) l9 in
        GENL [`x:real`; `y:real`] (DISCH (concl lin) (c1092moc_arith [b] `x <= &2`)) in
      let cutW =
        let e = MP (SPECL (c1092moc_own 9) C1092MOC_CENTER_CHART) (c1092moc_unit 9) in
        let bc = MP (SPECL C1092MPPE_V C1092MOC_BOTTOM_CUT) (ASSUME C1092MOC_CTX) in
        c1092moc_arith [e; bc] (mk_binop `(<=):real->real->bool` (list_mk_comb(`lcy`, tW)) `&0`) in
      let s = wfact (win `&543 / &500` `&0`) m9 in
      let t = wfact (win `&1` `--(&39 / &100)`) (bot `&161 / &100`) in
      let b = wfact (win `&1` `&2 / &5`) (bot `&12 / &5`) in
      let e = wfact (mk_neg (win `&1` `--(&2 / &5)`)) (CONV_RULE C1092MOC_CODE_CONV (ASSUME C1092MOC_OMIT)) in
      let apartW =
        let tm = list_mk_comb(`ldisj`, cv @ tW) in
        let eq = (REWRITE_CONV[ldisj] THENC convC THENC convW) tm in
        EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real`
          (SPECL [`y + &2`; `&4 - (x + &2)`] (c1092moc_apart 5 9)))) in
      let crossing = c1092moc_apply2 ALL_CONV (SPECL (cv @ tW @ [`cC:real`; `--sC`; z]) C1092MWC_POINT)
        [cu; apos; c1092moc_punit 9 tW; pos; REFL `cC:real`; sideC; capC; cp; angle; unitAngle;
         p; q; m; lowerV; s; t; b; e; wallW; cutW; apartW]
        [range; cp; sine; shape] in
      let tA, eqsA = c1092moc_layers_of cv [C1092MOC_SWAP; c1092moc_tr `--(&2)` `--(&2)`] in
      let tR, eqsR = c1092moc_layers 10 [C1092MOC_Y] in
      let convAR = c1092moc_conv (eqsA @ eqsR) in
      let ain x y = list_mk_comb(`linside`, tA @ [x; y]) in
      let ZARITH = REAL_ARITH `forall z. (&2 + z) + --(&2) = z` in
      let across = EQ_MP (SYM ((convAR THENC REWRITE_CONV[ZARITH]) (ain `&3` `&2 + C1092WPS_half cC (--sC)`)))
                         (CONJUNCT2 crossing) in
      let apartA =
        let tm = list_mk_comb(`ldisj`, tA @ tR) in
        let eq = (REWRITE_CONV[ldisj] THENC convAR THENC GEN_REWRITE_CONV ONCE_DEPTH_CONV [act] THENC
                  c1092moc_conv eqs5 THENC
                  REWRITE_CONV[REAL_ARITH `forall x. (x + --(&2)) + &2 = x`; REAL_ARITH `forall y. &4 - ((y + --(&2)) + &2) = &4 - y`]) tm in
        EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real` (SPECL [`x:real`; `&4 - y`] (c1092moc_apart 5 10)))) in
      let f = c1092moc_apply2 convAR (SPECL (tA @ tR @ [z]) C1092ICC_IMPOSSIBLE)
        [c1092moc_unit_of cu tA; apos; c1092moc_punit 10 tR; pos; sideC; cp; p; outer; zp; halfSmall;
         unitAngle; across; c1092moc_plcont 10 [C1092MOC_Y]; c1092moc_seed 10 (`&1543 / &500`, `&2`);
         CONJUNCT2 (CONJUNCT2 neighbor); apartA]
        [shape; sine; lowerV; lowerU; angle] in
      CCONTR (cin `&0` `&0`) f in
    DISJ_CASES (SPEC `&0 <= sC` EXCLUDED_MIDDLE) pos_branch neg_branch in
  c1092moc_choose cv ex (CONV_RULE convC center);;
let C1092MOC_BOTTOM_CENTER = c1092moc_close 5 "&2" "&2" (c1092moc_bottom_center ());;
