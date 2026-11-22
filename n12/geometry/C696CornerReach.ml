(* ========================================================================= *)
(* Port of Compact/Bridge/C696CornerReach.lean (namespace N12Compact.        *)
(* C696CornerReach).  (Lean header: "Source only, uncompiled".)  The         *)
(* original C696 positive central frame, if it misses the center, forces the *)
(* actual left singleton (owners p 1 = mask 2) to own its inner corner.      *)
(* Conventions of C696WallCycle.ml: owners p i is the owner of mask          *)
(* EL i c696ssp_owner_masks; the frame A : OpenSquare is cA sA uA vA aA with *)
(* unit normal and positive side, Normal is c977cc_normal, shape aA = l.     *)
(* SouthwestCornerTranspose.point = SCT_POINT.  Tag C696CK_.                 *)
(* ========================================================================= *)

needs "n12/geometry/C696CentralReach.ml";;
needs "n12/geometry/SouthwestCornerTranspose.ml";;

let C696CK_A = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`];;
let c696ck_ain x y = list_mk_comb(`linside`, C696CK_A @ [x; y]);;
let c696ck_oin m x y = list_mk_comb(`linside`, c696ssp_q m @ [x; y]);;
let c696ck_equiv m = list_mk_forall([`x:real`; `y:real`], mk_eq(c696ck_ain `x:real` `y:real`, c696ck_oin m `x:real` `y:real`));;
(* a query point of owner idx (inside / outside) *)
let c696ck_q idx p inside =
  let lab = C696SSP_LABEL idx in if inside then c696ssp_inside lab p else c696ssp_outside lab p;;
let c696ck_toa eqv th = let args = snd (strip_comb (concl th)) in EQ_MP (SYM (SPECL [el 5 args; el 6 args] eqv)) th;;
(* ldisj with A (A in first or second position) from the owner apartness and equivalent *)
let c696ck_ldisj eqv m n afirst =
  let ap = REWRITE_RULE[ldisj] (MP (SPEC_ALL (oo_apart `c696ssp_family` m n)) C696SSP_HH) in
  let tm = if afirst then list_mk_comb(`ldisj`, C696CK_A @ c696ssp_q n)
           else list_mk_comb(`ldisj`, c696ssp_q m @ C696CK_A) in
  EQ_MP (SYM (REWRITE_CONV[ldisj; eqv] tm)) ap;;

(* Lean: apart (private) is oo_apart *)

(* Lean: left_corner *)
let C696CK_LEFT_CORNER =
  let hyps = [`cA * cA + sA * sA = &1`; `&0 < aA`; `c977cc_normal cA sA`; `aA:real = l`; c696ck_equiv 256;
              mk_neg (c696ck_oin 256 `&2` `&2`)] in
  let ha = ASSUME (list_mk_conj hyps) in
  let [u; pos; nrm; shape; eqv; mc] = CONJUNCTS ha in
  let side = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP in
  let missing = ASSUME (mk_neg (c696ck_oin 2 `&1` `&1`)) in
  let cp = UNDISCH (SPEC_ALL C696CR_CENTRAL_POINTS) in
  let alow = c696ck_toa eqv (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 cp))) in
  let reach = MP (SPECL (c696ssp_q 1 @ C696CK_A @ c696ssp_q 2) SCT_POINT)
    (end_itlist CONJ
      [MP (SPECL (C696SSP_VARS @ [`2`]) OO_UNIT) C696SSP_NP; nrm; SYM shape;
       MP (REAL_ARITH `aA:real = l /\ &1 < l ==> &1 < aA`) (CONJ shape side);
       MP (SPECL (C696SSP_VARS @ [`2`]) OO_BOX) C696SSP_NP;
       c696ck_q 1 (`&457 / &500`, `&1`) true; c696ck_q 1 (`&1`, `&28 / &25`) true;
       c696ck_q 1 (`&19 / &25`, `&187 / &100`) true; missing; c696ck_q 1 (`&457 / &500`, `&2`) false;
       c696ck_toa eqv (c696ck_q 6 (`&33 / &20`, `&33 / &20`) true);
       c696ck_toa eqv (c696ck_q 6 (`&2`, `&87 / &50`) true);
       c696ck_toa eqv (c696ck_q 6 (`&87 / &50`, `&2`) true); alow;
       c696ck_q 0 (`&28 / &25`, `&1`) true; c696ck_q 0 (`&87 / &50`, `&1`) true;
       c696ck_ldisj eqv 2 256 false; c696ck_ldisj eqv 256 1 true]) in
  let f = MP (NOT_ELIM mc) (EQ_MP (SPECL [`&2`; `&2`] eqv) reach) in
  let th = CCONTR (c696ck_oin 2 `&1` `&1`) f in
  c696wc_close (c696wc_fix (GENL C696CK_A (DISCH (concl ha) th)));;
