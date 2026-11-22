(* ========================================================================= *)
(* Port of Compact/Bridge/C696WallCycle.lean (namespace N12Compact.          *)
(* C696WallCycle).  Uniform consequences of the actual C696 ownership        *)
(* assignment (C696AN_EXACT_ASSIGNMENT).  Conventions of SideSignPacking.ml: *)
(* owners p i is the owner 5-tuple of mask EL i c696ssp_owner_masks          *)
(* (literal masks 4096, 8192, 16384, 32768 for i = 8..11).  ExactMarkers /   *)
(* AuxExact are OO_MARKERS / OO_AUX_EXACT forms; queryInsidePoints /         *)
(* queryOutsidePoints membership (inside_query / outside_query) are the      *)
(* producers c696wc_inside_query i (x, y) / c696wc_outside_query i (x, y),   *)
(* which fail when the point is not in the query list.  wallFrame p i is the *)
(* 5-tuple C696WC_FRAMES.(i) (pullX / pullY / pullSwap as in p2_base,        *)
(* LCONT_PULLX etc.); centerX / centerY are lcx / lcy.  WallLowerCenterBarrier. *)
(* center_above = WLCB_CENTER_ABOVE, WallLowerReach.point = WLR_POINT.       *)
(* Tag C696WC_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/AuxiliaryNecessity.ml";;
needs "n12/geometry/WallLowerCenterBarrier.ml";;
needs "n12/geometry/WallLowerReach.ml";;

let C696WC_VARS = C696SSP_VARS;;
let C696WC_HYP = C696SSP_HYP;;
(* HYP |- c696ssp_exact_assignment c1 c2 a b l *)
let c696wc_exact = UNDISCH (SPEC_ALL C696AN_EXACT_ASSIGNMENT);;
let c696wc_fix th = PROVE_HYP c696wc_exact th;;
let c696wc_close th = GENL C696WC_VARS (DISCH C696WC_HYP th);;

(* Lean: owners_markers *)
let C696WC_OWNERS_MARKERS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c696ssp_family /\ i < 12
     ==> forall k. k < 16
         ==> (linside (ooc c1 c2 a b l (EL i c696ssp_owner_masks)) (oos c1 c2 a b l (EL i c696ssp_owner_masks))
                      (oou c1 c2 a b l (EL i c696ssp_owner_masks)) (oov c1 c2 a b l (EL i c696ssp_owner_masks)) l
                      (marker k$1) (marker k$2) <=> k IN bitset (EL i c696ssp_owner_masks))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OO_MARKERS THEN
  EXISTS_TAC `c696ssp_family` THEN ASM_SIMP_TAC[C696SSP_OWNERMASKS_MEM]);;

(* Lean: side_gt *)
let C696WC_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`, ACCEPT_TAC OO_SIDE);;

(* Lean: side_le *)
let C696WC_SIDE_LE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> l <= &1001 / &1000`, ACCEPT_TAC OO_SIDE_LE);;

(* Lean: actual_auxiliary *)
let C696WC_ACTUAL_AUXILIARY = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c696ssp_family
     ==> forall i j. i < 12 /\ j < 20
         ==> (linside (ooc c1 c2 a b l (EL i c696ssp_owner_masks)) (oos c1 c2 a b l (EL i c696ssp_owner_masks))
                      (oou c1 c2 a b l (EL i c696ssp_owner_masks)) (oov c1 c2 a b l (EL i c696ssp_owner_masks)) l
                      (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=> j IN EL i c696ssp_auxiliary_vector)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C696AN_EXACT_ASSIGNMENT) THEN ASM_REWRITE_TAC[c696ssp_exact_assignment] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[OO_AUX_EXACT]);;

(* Lean: inside_query / outside_query (producers at a literal owner index i and point) *)
let c696wc_inside_query i (x, y) = c696wc_close (c696wc_fix (c696ssp_inside (C696SSP_LABEL i) (x, y)));;
let c696wc_outside_query i (x, y) = c696wc_close (c696wc_fix (c696ssp_outside (C696SSP_LABEL i) (x, y)));;

(* Lean: wallOwner, wallFrame (as lcont theorems of the frames, the frame is their tuple) *)
let C696WC_WALL_OWNER = [8; 9; 10; 11];;
let c696wc_box i = MP (SPECL (C696WC_VARS @ [mk_small_numeral (el i [4096; 8192; 16384; 32768])]) OO_BOX)
                      C696SSP_NP;;
let C696WC_FRAME_BOX =
  [| c696wc_box 0;
     MATCH_MP LCONT_PULLSW (c696wc_box 1);
     MATCH_MP LCONT_PULLX (MATCH_MP LCONT_PULLY (c696wc_box 2));
     MATCH_MP LCONT_PULLX (MATCH_MP LCONT_PULLY (MATCH_MP LCONT_PULLSW (c696wc_box 3))) |];;
let C696WC_FRAMES = Array.map (fun th -> snd (strip_comb (concl th))) C696WC_FRAME_BOX;;

(* Lean: frame_inside (private): linside (frame i) x y <=> linside (owner) (wallPoint i (x, y)) *)
let c696wc_frame_conv =
  REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* Lean: frame_side / frame_box (private) and the frame unit normal *)
let c696wc_frame_unit i =
  let f = C696WC_FRAMES.(i) in
  let ou = MP (SPECL (C696WC_VARS @ [mk_small_numeral (el i [4096; 8192; 16384; 32768])]) OO_UNIT) C696SSP_NP in
  let sq x = mk_binop `( * ):real->real->real` x x in
  let tm = mk_eq(mk_binop `(+):real->real->real` (sq (el 0 f)) (sq (el 1 f)), `&1`) in
  MP (REAL_RING (mk_imp(concl ou, tm))) ou;;

(* Lean: frame_owned / frame_missing (private) *)
let c696wc_frame_fact i (x, y) inside =
  let tm = list_mk_comb(`linside`, C696WC_FRAMES.(i) @ [x; y]) in
  let e = c696wc_frame_conv tm in
  let args = snd (strip_comb (rhs (concl e))) in
  let lab = C696SSP_LABEL (el i C696WC_WALL_OWNER) in
  if inside then EQ_MP (SYM e) (c696ssp_inside lab (el 5 args, el 6 args))
  else EQ_MP (SYM (AP_TERM `(~)` e)) (c696ssp_outside lab (el 5 args, el 6 args));;

let c696wc_progress i =
  let f = C696WC_FRAMES.(i) in
  let side = MP (SPECL C696WC_VARS OO_SIDE) C696SSP_NP in
  let ff = c696wc_frame_fact i in
  let p = ff (`&457 / &500`, `&2`) true and q = ff (`&1`, `&12 / &5`) true
  and w = ff (`&1`, `&87 / &50`) false and d = ff (`&87 / &50`, `&2`) false
  and t = ff (`&33 / &20`, `&47 / &20`) false in
  let base = [c696wc_frame_unit i; side; C696WC_FRAME_BOX.(i); p; q; w] in
  CONJ (MP (SPECL f WLCB_CENTER_ABOVE) (end_itlist CONJ (base @ [t])))
       (MP (SPECL f WLR_POINT) (end_itlist CONJ (base @ [d])));;

(* Lean: frame_progress  (the conjunction over the four frames i = 0..3) *)
let C696WC_FRAME_PROGRESS =
  c696wc_close (c696wc_fix (end_itlist CONJ (map c696wc_progress (0 -- 3))));;

(* centres of the frames in terms of the owners *)
let c696wc_centre i target =
  let f = C696WC_FRAMES.(i) in
  let ou = MP (SPECL (C696WC_VARS @ [mk_small_numeral (el i [4096; 8192; 16384; 32768])]) OO_UNIT) C696SSP_NP in
  MP (prove(mk_imp(concl ou, mk_eq(list_mk_comb(`lcy`, f), target)),
            REWRITE_TAC[lcx; lcy] THEN CONV_TAC REAL_RING)) ou;;

(* Lean: center_cuts *)
let C696WC_CENTER_CUTS =
  let q m = c696ssp_q m in
  let lcx_ m = list_mk_comb(`lcx`, q m) and lcy_ m = list_mk_comb(`lcy`, q m) in
  let four t = mk_binop `(-):real->real->real` `&4` t in
  let eqs = [c696wc_centre 0 (lcy_ 4096); c696wc_centre 1 (lcx_ 8192);
             c696wc_centre 2 (four (lcy_ 16384)); c696wc_centre 3 (four (lcx_ 32768))] in
  let prog = CONJUNCTS (UNDISCH (SPEC_ALL C696WC_FRAME_PROGRESS)) in
  let centres = map (fun i -> el (2 * i) prog) (0 -- 3) in
  let goal = list_mk_conj
    [mk_binop `(<):real->real->bool` `&21 / &10` (lcy_ 4096);
     mk_binop `(<):real->real->bool` `&21 / &10` (lcx_ 8192);
     mk_binop `(<):real->real->bool` (lcy_ 16384) `&19 / &10`;
     mk_binop `(<):real->real->bool` (lcx_ 32768) `&19 / &10`] in
  c696wc_close (MP (REAL_ARITH (mk_imp(list_mk_conj (map concl (eqs @ centres)), goal)))
                   (end_itlist CONJ (eqs @ centres)));;

(* Lean: owned_points *)
let C696WC_OWNED_POINTS =
  let prog = CONJUNCTS (UNDISCH (SPEC_ALL C696WC_FRAME_PROGRESS)) in
  let pts = map (fun i -> let th = el (2 * i + 1) prog in
                          EQ_MP (c696wc_frame_conv (concl th)) th) (0 -- 3) in
  c696wc_close (end_itlist CONJ pts);;
