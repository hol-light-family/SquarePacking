(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/Origins.lean                        *)
(* (namespace N12Compact.C1092MMMPOrigins).  Actual MMMP top reach, left and *)
(* right origins, and the NW left crosspoint.  Conventions of                *)
(* CP_C1092_MMMPEntrance.ml: owners p i is the OriginalOwners 5-tuple at     *)
(* mask EL i c1092wc_code (0..11 -> 3,12,48,192,256,512,1024,2048,4096,8192, *)
(* 16384,32768; side l); WallContext p mmmp is                               *)
(* c1092wc_ctx c1 c2 a b l c1092mmpe_mmmp.  Transform.pull g (swap, rX, rY)  *)
(* is pullSwap (pullY (pullX q)) restricted to the true flags, built from    *)
(* LINSIDE_PULLX / PULLY / PULLSW; translated is CCIP_INSIDE_TRANSLATED;     *)
(* container_transform via LCONT_PULLX / PULLY / PULLSW.                     *)
(* WallLowerReach.point = WLR_POINT, boundary_origin = OCWPBO_BOUNDARY_ORIGIN,*)
(* C1092MMMPMarkerHalfpoint.point = C1092MMH_POINT,                          *)
(* C981CompletionCrosspoint.point = C981CP_POINT, inside_segment (here the   *)
(* horizontal case) = OO_HORIZONTAL_SEGMENT.  Seeds / corner points of the   *)
(* owners come from oo_seed (OriginalOwners.seed), owners_disjoint from      *)
(* oo_apart.  Tag C1092MO_.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMPEntrance.ml";;
needs "n12/geometry/CP_C1092_MMMP_MarkerHalfpoint.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;

(* Lean: side_gt *)
let C1092MO_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`,
  REWRITE_TAC[OO_SIDE]);;

(* Lean: side_same  (every owner has the side term l) *)
let C1092MO_SIDE_SAME = prove
 (`forall l:real. l = l`, REWRITE_TAC[]);;

(* Lean: marker_point *)
let C1092MO_MARKER_POINT = prove
 (parse_term (Printf.sprintf "!%s i j. %s /\\ i < 12 /\\ j < 16 /\\ j IN bitset (EL i c1092wc_code) ==> linside %s (marker j$1) (marker j$2)"
    C1092AE_P C1092AE_HYP
    "(ooc c1 c2 a b l (EL i c1092wc_code)) (oos c1 c2 a b l (EL i c1092wc_code)) (oou c1 c2 a b l (EL i c1092wc_code)) (oov c1 c2 a b l (EL i c1092wc_code)) l"),
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`i:num`]) C1092WC_OWNERS_MARKERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]);;

(* ---- forward toolkit (literal masks; hyps NPACK, IMAGE, WallContext) ---- *)
let C1092MO_NP = `NPACK c1 c2 a b l`;;
let C1092MO_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`;;
let C1092MO_CTX = `c1092wc_ctx c1 c2 a b l c1092mmpe_mmmp`;;
let C1092MO_CODE_CONV = REWRITE_CONV (Array.to_list C1092WC_CODE_EL);;
let C1092MO_MASKS = [3;12;48;192;256;512;1024;2048;4096;8192;16384;32768];;
let c1092mo_own i =
  map (fun f -> list_mk_comb(f, C1092MMPE_V @ [mk_small_numeral (el i C1092MO_MASKS)]))
    [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c1092mo_in i x y = list_mk_comb(`linside`, c1092mo_own i @ [x; y]);;
let c1092mo_hh () = CONJ (ASSUME C1092MO_NP) (ASSUME C1092MO_IMG);;
let c1092mo_hc () = CONJ (ASSUME C1092MO_NP) (CONJ (ASSUME C1092MO_IMG) (ASSUME C1092MO_CTX));;
(* use an EL-form packing theorem with hypothesis NPACK /\ IMAGE /\ ctx (or NPACK /\ ctx) *)
let c1092mo_use th =
  let th1 = SPECL C1092MMPE_V th in
  let h = if lhand (concl th1) = mk_conj(C1092MO_NP, C1092MO_CTX)
          then CONJ (ASSUME C1092MO_NP) (ASSUME C1092MO_CTX) else c1092mo_hc () in
  CONV_RULE C1092MO_CODE_CONV (MP th1 h);;
let c1092mo_side () = MP (SPECL C1092MMPE_V OO_SIDE) (ASSUME C1092MO_NP);;
let c1092mo_unit i = MP (SPECL (C1092MMPE_V @ [mk_small_numeral (el i C1092MO_MASKS)]) OO_UNIT) (ASSUME C1092MO_NP);;
let c1092mo_box i = MP (SPECL (C1092MMPE_V @ [mk_small_numeral (el i C1092MO_MASKS)]) OO_BOX) (ASSUME C1092MO_NP);;
let c1092mo_seed i (x, y) =
  MP (SPECL C1092MMPE_V (oo_inst `c1092wc_family` (oo_seed (el i C1092MO_MASKS) (x, y)))) (c1092mo_hh ());;
let c1092mo_apart i j =
  REWRITE_RULE[ldisj] (MP (SPECL C1092MMPE_V
    (oo_apart `c1092wc_family` (el i C1092MO_MASKS) (el j C1092MO_MASKS))) (c1092mo_hh ()));;
(* a point of owner j is not in owner i *)
let c1092mo_excl i j pt =
  let args = snd (strip_comb (concl pt)) in
  let d2 = SPECL [el 5 args; el 6 args] (c1092mo_apart i j) in
  let a = lhand (rand (concl d2)) in
  NOT_INTRO (DISCH a (MP (NOT_ELIM d2) (CONJ (ASSUME a) pt)));;

(* layers of a transformed owner, innermost first: (lemma, extra args) *)
let C1092MO_X = (LINSIDE_PULLX, []) and C1092MO_Y = (LINSIDE_PULLY, [])
and C1092MO_SW = (LINSIDE_PULLSW, []);;
let c1092mo_tr dx dy = (CCIP_INSIDE_TRANSLATED, [dx; dy]);;
(* tuples t0 = owner, t1, .., tn and the unfolding equations (outermost first) *)
let c1092mo_layers i layers =
  let step (cur, eqs) (pth, extra) =
    let t = SPECL (cur @ extra @ [`x:real`; `y:real`]) pth in
    let args = snd (strip_comb (lhs (concl t))) in
    ([el 0 args; el 1 args; el 2 args; el 3 args; el 4 args], GENL [`x:real`; `y:real`] t :: eqs) in
  rev_itlist (fun l acc -> step acc l) layers (c1092mo_own i, []);;
let c1092mo_conv eqs =
  EVERY_CONV (map (fun e -> GEN_REWRITE_CONV ONCE_DEPTH_CONV [e]) eqs) THENC
  ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;
let c1092mo_punit i t =
  let c = el 0 t and s = el 1 t in
  let tm = mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                   (mk_binop `( * ):real->real->real` s s), `&1`) in
  MP (prove(mk_imp(concl (c1092mo_unit i), tm), CONV_TAC REAL_RING)) (c1092mo_unit i);;
let c1092mo_plcont i layers =
  itlist (fun (pth, _) acc ->
    MATCH_MP (if pth == LINSIDE_PULLX then LCONT_PULLX else if pth == LINSIDE_PULLY then LCONT_PULLY
              else LCONT_PULLSW) acc) (rev layers) (c1092mo_box i);;
let C1092MO_BOX_Y = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;
let C1092MO_BOX_XY = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;

(* discharge the antecedents of spec from facts, up to conv *)
let c1092mo_apply conv spec facts =
  let ants = conjuncts (lhand (concl spec)) in
  let pa tm =
    try find (fun f -> aconv (concl f) tm) facts with Failure _ ->
    let eq = conv tm in
    let r = rhs (concl eq) in
    if r = `true` then EQT_ELIM eq else
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) r) facts)
    with Failure _ -> failwith ("c1092mo_apply: " ^ string_of_term tm) in
  CONV_RULE conv (MP spec (end_itlist CONJ (map pa ants)));;

(* close  !c1 .. l. HYP /\ CTX ==> linside (EL i code) x y  from a literal-mask theorem *)
let c1092mo_close i x y th =
  prove(c1092mmpe_stmt i x y,
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN ACCEPT_TAC th);;

let c1092mo_pos () = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) (c1092mo_side ());;

(* Lean: top_far *)
let c1092mo_top_far () =
  let top = c1092mo_use C1092MMPE_TOP_PAIR and ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR
  and nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let layers = [C1092MO_X; C1092MO_Y; C1092MO_SW] in
  let t, eqs = c1092mo_layers 11 layers in
  c1092mo_apply (c1092mo_conv eqs) (SPECL t WLR_POINT)
    [c1092mo_punit 11 t; c1092mo_side (); c1092mo_plcont 11 layers;
     c1092mo_seed 11 (`&2`, `&1543 / &500`); CONJUNCT1 top;
     c1092mo_excl 11 6 (CONJUNCT2 ne); c1092mo_excl 11 7 (CONJUNCT1 nw)];;
let C1092MO_TOP_FAR = c1092mo_close 11 "&36 / &25" "&3" (c1092mo_top_far ());;

(* Lean: top_halfpoint *)
let c1092mo_top_halfpoint () =
  let rr tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm) in
  MP (SPECL (c1092mo_own 11 @ [`&36 / &25`; `&8 / &5`; `&3`; `&3 / &2`]) OO_HORIZONTAL_SEGMENT)
    (end_itlist CONJ [c1092mo_top_far (); CONJUNCT1 (c1092mo_use C1092MMPE_TOP_PAIR);
       rr `&36 / &25 < &8 / &5`; rr `&36 / &25 <= &3 / &2`; rr `&3 / &2 <= &8 / &5`]);;
let C1092MO_TOP_HALFPOINT = c1092mo_close 11 "&3 / &2" "&3" (c1092mo_top_halfpoint ());;

(* boundary_origin for B = g.pull (owners ib), K = g.pull (owners ik); xy = g.apply x y *)
let c1092mo_origin layers ib ik b ell facts xy =
  let tB, eqB = c1092mo_layers ib layers and tK, eqK = c1092mo_layers ik layers in
  let disj =
    let tm = list_mk_comb(`ldisj`, tK @ tB) in
    let eq = (REWRITE_CONV[ldisj] THENC c1092mo_conv eqK THENC c1092mo_conv eqB) tm in
    EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real` (SPECL xy (c1092mo_apart ik ib)))) in
  let facts = [c1092mo_punit ib tB; c1092mo_punit ik tK; c1092mo_pos (); c1092mo_side ();
               REFL `l:real`; MATCH_MP C1092MO_BOX_Y (c1092mo_plcont ib layers);
               MATCH_MP C1092MO_BOX_XY (c1092mo_plcont ik layers); disj] @ facts in
  c1092mo_apply (c1092mo_conv (eqB @ eqK)) (SPECL (tB @ tK @ [b; ell]) OCWPBO_BOUNDARY_ORIGIN) facts;;

(* Lean: left_origin *)
let c1092mo_left_origin () =
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  c1092mo_origin [C1092MO_Y; C1092MO_SW] 8 3 `&457 / &500` `&87 / &50`
    [c1092mo_seed 8 (`&457 / &500`, `&2`); CONJUNCT1 wa; c1092mo_seed 3 (`&457 / &500`, `&3`);
     c1092mo_seed 3 (`&1`, `&3`); c1092mo_excl 3 11 (c1092mo_top_halfpoint ())]
    [`y:real`; `&4 - x`];;
let C1092MO_LEFT_ORIGIN = c1092mo_close 8 "&1" "&2" (c1092mo_left_origin ());;

(* Lean: northeast_halfpoint *)
let c1092mo_northeast_halfpoint () =
  let ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR and nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  let t, eqs = c1092mo_layers 6 [C1092MO_X; C1092MO_SW; c1092mo_tr `&2` `&2`] in
  c1092mo_apply (c1092mo_conv eqs) (SPECL (t @ [`&43 / &500`]) C1092MMH_POINT)
    [c1092mo_punit 6 t; c1092mo_pos (); c1092mo_side ();
     c1092mo_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT2 ne; CONJUNCT1 ne;
     c1092mo_excl 6 7 (CONJUNCT1 nw);
     c1092mo_excl 6 11 (c1092mo_seed 11 (`&2`, `&1543 / &500`));
     c1092mo_excl 6 2 (c1092mo_seed 2 (`&3`, `&3`));
     c1092mo_excl 6 10 (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 wa)))];;
let C1092MO_NORTHEAST_HALFPOINT = c1092mo_close 6 "&5 / &2" "&3" (c1092mo_northeast_halfpoint ());;

(* Lean: right_origin *)
let c1092mo_right_origin () =
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  c1092mo_origin [C1092MO_X; C1092MO_Y; C1092MO_SW] 10 2 `&457 / &500` `&87 / &50`
    [c1092mo_seed 10 (`&1543 / &500`, `&2`); CONJUNCT1 (CONJUNCT2 (CONJUNCT2 wa));
     c1092mo_seed 2 (`&1543 / &500`, `&3`); c1092mo_seed 2 (`&3`, `&3`);
     c1092mo_excl 2 6 (c1092mo_northeast_halfpoint ())]
    [`&4 - y`; `&4 - x`];;
let C1092MO_RIGHT_ORIGIN = c1092mo_close 10 "&3" "&2" (c1092mo_right_origin ());;

(* Lean: northwest_left *)
let c1092mo_northwest_left () =
  let nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR and top = c1092mo_use C1092MMPE_TOP_PAIR in
  let t, eqs = c1092mo_layers 7 [C1092MO_X; C1092MO_SW] in
  c1092mo_apply (c1092mo_conv eqs) (SPECL t C981CP_POINT)
    [c1092mo_punit 7 t; c1092mo_pos (); c1092mo_side ();
     CONJUNCT2 nw; CONJUNCT1 nw; c1092mo_seed 7 (`&33 / &20`, `&47 / &20`);
     c1092mo_excl 7 6 (c1092mo_seed 6 (`&47 / &20`, `&47 / &20`));
     c1092mo_excl 7 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`));
     c1092mo_excl 7 11 (CONJUNCT1 top);
     c1092mo_excl 7 11 (c1092mo_top_halfpoint ())];;
let C1092MO_NORTHWEST_LEFT = c1092mo_close 7 "&3 / &2" "&2" (c1092mo_northwest_left ());;
