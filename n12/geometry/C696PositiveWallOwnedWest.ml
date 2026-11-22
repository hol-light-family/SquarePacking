(* ========================================================================= *)
(* Port of Compact/Bridge/C696PositiveWallOwnedWest.lean (namespace          *)
(* N12Compact.C696PositiveWallOwnedWest).  (Lean header: "Source only,       *)
(* uncompiled".)  A complete original C696 orientation sector at each of the *)
(* four walls.  Conventions of C696WallCycle.ml / C696CentralReach.ml:       *)
(* frame q i is the tuple c696cr_frame i idx of owner idx (owners p i = mask *)
(* EL i c696ssp_owner_masks).  The wall frame W : OpenSquare is              *)
(* cW sW uW vW aW with unit normal and positive side; Normal W.c W.s is      *)
(* c977cc_normal cW sW; shape is aW = l; W.loV is vW.  Statements over      *)
(* i : Fin 4 are the conjunction over i = 0..3.  CornerBudgetReach.          *)
(* upper_left = CBR_UPPER_LEFT; PositiveWallOwnedWestFaces lower_face /      *)
(* upper_v / tilt = PWOWF_LOWER_FACE / PWOWF_UPPER_V / PWOWF_TILT;           *)
(* PositiveWallOwnedWestCorner.impossible = PWOWC_IMPOSSIBLE.  Tag C696PW_.  *)
(* ========================================================================= *)

needs "n12/geometry/C696CentralReach.ml";;
needs "n12/geometry/CornerBudgetReach.ml";;
needs "n12/geometry/PositiveWallOwnedWestCorner.ml";;
needs "n12/geometry/PositiveWallOwnedWestFaces.ml";;

(* Lean: cornerOwner, centralOwner, singletonOwner *)
let C696PW_CORNER_OWNER = [5; 2; 2; 5] and C696PW_CENTRAL_OWNER = [6; 6; 7; 7]
and C696PW_SINGLETON_OWNER = [1; 0; 4; 3];;

let C696PW_W = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;
let c696pw_win x y = list_mk_comb(`linside`, C696PW_W @ [x; y]);;
let c696pw_fin i idx x y = list_mk_comb(`linside`, c696cr_frame i idx @ [x; y]);;
let c696pw_wall i = el i C696WC_WALL_OWNER;;
let c696pw_equiv i =
  list_mk_forall([`x:real`; `y:real`],
    mk_eq(c696pw_win `x:real` `y:real`, c696pw_fin i (c696pw_wall i) `x:real` `y:real`));;
(* unit, side, Normal, shape, equivalent *)
let c696pw_whyps i =
  [`cW * cW + sW * sW = &1`; `&0 < aW`; `c977cc_normal cW sW`; `aW:real = l`; c696pw_equiv i];;
let c696pw_side () = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP;;

(* a frame fact of the wall owner read on W *)
let c696pw_tow eqv th =
  let neg = is_neg (concl th) in
  let args = snd (strip_comb (if neg then rand (concl th) else concl th)) in
  let e = SPECL [el 5 args; el 6 args] eqv in
  if neg then EQ_MP (SYM (AP_TERM `(~)` e)) th else EQ_MP (SYM e) th;;
(* ~linside W x y from a point of the frame of owner idx (frame_apart with the wall) *)
let c696pw_wapart eqv i idx th =
  let args = snd (strip_comb (concl th)) in
  let x = el 5 args and y = el 6 args in
  let d = SPECL [x; y] (c696cr_apart i (c696pw_wall i) idx) in
  let fw = lhand (rand (concl d)) in
  c696pw_tow eqv (NOT_INTRO (DISCH fw (MP (NOT_ELIM d) (CONJ (ASSUME fw) th))));;

(* Lean: frame_box (private) is c696cr_box *)

(* Lean: corner_outward *)
let c696pw_corner_outward i =
  let ci = el i C696PW_CORNER_OWNER in
  let side = c696pw_side () in
  MP (SPECL (c696cr_frame i ci) CBR_UPPER_LEFT)
     (end_itlist CONJ [c696cr_unit i ci; MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) side; side;
        c696cr_box i ci;
        c696cr_fact i ci (`&1`, `&1543 / &500`) true; c696cr_fact i ci (`&457 / &500`, `&3`) true;
        c696cr_fact i ci (`&8 / &5`, `&3`) false; c696cr_fact i ci (`&1`, `&12 / &5`) false]);;
let C696PW_CORNER_OUTWARD =
  c696wc_close (c696wc_fix (end_itlist CONJ (map c696pw_corner_outward (0 -- 3))));;

let c696pw_wside shape = MP (REAL_ARITH `aW:real = l /\ &1 < l ==> &1 < aW`) (CONJ shape (c696pw_side ()));;
let c696pw_wbox i eqv =
  let fb = REWRITE_RULE[lcont] (c696cr_box i (c696pw_wall i)) in
  EQ_MP (SYM (REWRITE_CONV[lcont; eqv] (list_mk_comb(`lcont`, C696PW_W)))) fb;;

(* Lean: faces_of_missing (private) *)
let c696pw_faces i [u; pos; nrm; shape; eqv] mw =
  let wl = c696pw_wall i in
  let wside = c696pw_wside shape and box = c696pw_wbox i eqv in
  let marker = c696pw_tow eqv (c696cr_fact i wl (`&457 / &500`, `&2`) true)
  and hi12 = c696pw_tow eqv (c696cr_fact i wl (`&1`, `&12 / &5`) true) in
  let far = c696cr_fact i (el i C696PW_SINGLETON_OWNER) (`&19 / &25`, `&187 / &100`) true in
  let missingFar = c696pw_wapart eqv i (el i C696PW_SINGLETON_OWNER) far in
  let missingTop = c696pw_tow eqv (c696cr_fact i wl (`&457 / &500`, `&3`) false) in
  let missingOut = c696pw_wapart eqv i (el i C696PW_CORNER_OWNER) (c696pw_corner_outward i) in
  let lower = MP (SPECL C696PW_W PWOWF_LOWER_FACE) (end_itlist CONJ [nrm; marker; hi12; mw]) in
  let upper = MP (SPECL C696PW_W PWOWF_UPPER_V)
    (end_itlist CONJ [u; pos; nrm; wside; box; marker; hi12; mw; missingFar; missingTop; missingOut]) in
  let tilt = MP (SPECL [`cW:real`; `sW:real`; `aW:real`; `vW:real`] PWOWF_TILT)
    (end_itlist CONJ [nrm; wside; lower; upper]) in
  end_itlist CONJ [lower; upper; tilt];;

(* PositiveWallOwnedWestCorner.impossible applied to W and the corner frame *)
let c696pw_impossible i [u; pos; nrm; shape; eqv] faces =
  let ci = el i C696PW_CORNER_OWNER in
  let e = c696cr_frame i ci in
  let side = c696pw_side () in
  let hi12 = c696pw_tow eqv (c696cr_fact i (c696pw_wall i) (`&1`, `&12 / &5`) true) in
  let disj =
    let ap = c696cr_apart i ci (c696pw_wall i) in
    EQ_MP (SYM (REWRITE_CONV[ldisj; eqv] (list_mk_comb(`ldisj`, e @ C696PW_W)))) ap in
  MP (SPECL (C696PW_W @ e) PWOWC_IMPOSSIBLE)
     (end_itlist CONJ ([u; pos; c696cr_unit i ci; MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) side; nrm;
        c696pw_wside shape; c696pw_wbox i eqv; hi12] @ CONJUNCTS faces @
       [c696pw_corner_outward i; c696cr_fact i ci (`&1`, `&3`) true;
        c696cr_fact i ci (`&1`, `&1543 / &500`) true; disj]));;

(* a per-frame statement  !cW sW uW vW aW. hyps ==> concl  from a builder on the hypotheses *)
let c696pw_gen hyps build =
  let a = ASSUME (list_mk_conj hyps) in
  let parts = CONJUNCTS a in
  if length parts <> length hyps then failwith "c696pw_gen" else
  GENL C696PW_W (DISCH (concl a) (build parts));;
let c696pw_all f = c696wc_close (c696wc_fix (end_itlist CONJ (map f (0 -- 3))));;

let C696PW_FACES_OF_MISSING = c696pw_all (fun i ->
  c696pw_gen (c696pw_whyps i @ [mk_neg (c696pw_win `&1` `&2`)])
    (fun ps -> c696pw_faces i (fst (chop_list 5 ps)) (el 5 ps)));;

(* Lean: frame_point *)
let C696PW_FRAME_POINT = c696pw_all (fun i ->
  c696pw_gen (c696pw_whyps i) (fun ps ->
    let w12 = c696pw_win `&1` `&2` in
    CCONTR w12 (c696pw_impossible i ps (c696pw_faces i ps (ASSUME (mk_neg w12))))));;

let c696pw_west i = c696pw_fin i (el i C696PW_CENTRAL_OWNER) `&1` `&2`;;
let c696pw_missing_west i eqv west = c696pw_wapart eqv i (el i C696PW_CENTRAL_OWNER) west;;

(* Lean: frame_faces *)
let C696PW_FRAME_FACES = c696pw_all (fun i ->
  c696pw_gen (c696pw_whyps i @ [c696pw_west i]) (fun ps ->
    let hs = fst (chop_list 5 ps) in
    c696pw_faces i hs (c696pw_missing_west i (el 4 ps) (el 5 ps))));;

(* Lean: frame_excludes *)
let C696PW_FRAME_EXCLUDES = c696pw_all (fun i ->
  c696pw_gen (c696pw_whyps i @ [c696pw_west i]) (fun ps ->
    let hs = fst (chop_list 5 ps) in
    c696pw_impossible i hs (c696pw_faces i hs (c696pw_missing_west i (el 4 ps) (el 5 ps)))));;

(* Lean: canonical_sine_negative *)
let C696PW_NORMAL_OF_CANONICAL = prove
 (`forall c s. &0 <= s /\ abs s <= c /\ c * c + s * s = &1 ==> c977cc_normal c s`,
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REAL_ARITH_TAC);;
let C696PW_CANONICAL_SINE_NEGATIVE = c696pw_all (fun i ->
  c696pw_gen [`cW * cW + sW * sW = &1`; `&0 < aW`; `abs sW <= cW`; `aW:real = l`; c696pw_equiv i;
              c696pw_west i] (fun [u; pos; can; shape; eqv; west] ->
    let nn = `&0 <= sW` in
    let nrm = MP (SPECL [`cW:real`; `sW:real`] C696PW_NORMAL_OF_CANONICAL)
                 (end_itlist CONJ [ASSUME nn; can; u]) in
    let f = c696pw_impossible i [u; pos; nrm; shape; eqv]
              (c696pw_faces i [u; pos; nrm; shape; eqv] (c696pw_missing_west i eqv west)) in
    EQ_MP (REAL_ARITH `~(&0 <= sW) <=> sW < &0`) (NOT_INTRO (DISCH nn f))));;
