(* ========================================================================= *)
(* Port of Compact/Bridge/C696OwnedWestCorner.lean (namespace N12Compact.    *)
(* C696OwnedWestCorner).  (Lean header: "Source only, uncompiled".)          *)
(* Original C696 positive-bottom / negative-wall exclusion with the actual   *)
(* central west point owned.  Conventions of C696CornerReach.ml: owners p 0, *)
(* 1, 6, 8 are the owners of masks 1, 2, 256, 4096; the frames O, A, W are   *)
(* cO sO uO vO aO etc. with unit normal and positive side; Normal is         *)
(* c977cc_normal; W.s = --t; shapes are aO = l etc.  The canonical frame L   *)
(* of owners p 1 comes from CLF_CANONICAL_FRAME.  Used: CornerWallMarker-    *)
(* Cycle.impossible (CWMCY_IMPOSSIBLE, Data = cwmcy_data), PositiveCentral-  *)
(* WallAngleOrder.angle_order (PCWAO_ANGLE_ORDER), NegativeWallTopSeed.      *)
(* lower_face (NWTS_LOWER_FACE), NegativeWallMarkerCap.upper_face / upper_u  *)
(* / sector (NWMC_ thms), C696PositiveCorner.corner_faces (C696PC_CORNER_FACES), *)
(* normal_bounds (C977CC_NORMAL_BOUNDS).  Tag C696OW_.                       *)
(* ========================================================================= *)

needs "n12/geometry/C696CornerReach.ml";;
needs "n12/geometry/PositiveCentralWallAngleOrder.ml";;
needs "n12/geometry/CornerWallMarkerCycle.ml";;
needs "n12/geometry/NegativeWallMarkerCap.ml";;
needs "n12/geometry/NegativeWallTopSeed.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/CornerWallMarkerMixedBounds.ml";;

(* Lean: apart (private) is oo_apart *)

let C696OW_BOUNDARY = prove
 (`forall c s. cwmmb_boundary c s = c696cm_boundary c s`,
  REWRITE_TAC[CWMMB_BOUNDARY_DEF; c696cm_boundary]);;

let c696ow_sq n = map (fun v -> mk_var(v ^ n, `:real`)) ["c"; "s"; "u"; "v"; "a"];;
let C696OW_O = c696ow_sq "O" and C696OW_A = c696ow_sq "A" and C696OW_W = c696ow_sq "W"
and C696OW_L = c696ow_sq "L";;
let c696ow_in sq x y = list_mk_comb(`linside`, sq @ [x; y]);;
let c696ow_equiv sq m = list_mk_forall([`x:real`; `y:real`],
  mk_eq(c696ow_in sq `x:real` `y:real`, c696ck_oin m `x:real` `y:real`));;
let c696ow_unit sq = mk_eq(mk_binop `(+):real->real->real`
  (mk_binop `( * ):real->real->real` (el 0 sq) (el 0 sq)) (mk_binop `( * ):real->real->real` (el 1 sq) (el 1 sq)), `&1`);;
let c696ow_pos sq = mk_binop `(<):real->real->bool` `&0` (el 4 sq);;
let c696ow_shape sq = mk_eq(el 4 sq, `l:real`);;

(* a fact of owner m read on the frame sq (positive or negative) *)
let c696ow_to eqv th =
  let neg = is_neg (concl th) in
  let args = snd (strip_comb (if neg then rand (concl th) else concl th)) in
  let e = SPECL [el 5 args; el 6 args] eqv in
  if neg then EQ_MP (SYM (AP_TERM `(~)` e)) th else EQ_MP (SYM e) th;;
let c696ow_box eqv sq m =
  let fb = REWRITE_RULE[lcont] (MP (SPECL (C696SSP_VARS @ [mk_small_numeral m]) OO_BOX) C696SSP_NP) in
  EQ_MP (SYM (REWRITE_CONV[lcont; eqv] (list_mk_comb(`lcont`, sq)))) fb;;
let c696ow_ldisj e1 sq1 m e2 sq2 n =
  let ap = REWRITE_RULE[ldisj] (MP (SPEC_ALL (oo_apart `c696ssp_family` m n)) C696SSP_HH) in
  EQ_MP (SYM (REWRITE_CONV[ldisj; e1; e2] (list_mk_comb(`ldisj`, sq1 @ sq2)))) ap;;
let c696ow_arith hs tm = MP (REAL_ARITH (mk_imp(list_mk_conj (map concl hs), tm))) (end_itlist CONJ hs);;

let C696OW_HYPS =
  [c696ow_unit C696OW_O; c696ow_pos C696OW_O; c696ow_unit C696OW_A; c696ow_pos C696OW_A;
   c696ow_unit C696OW_W; c696ow_pos C696OW_W;
   `c977cc_normal cO sO`; `c977cc_normal cA sA`; `c977cc_normal cW t`; `sW = --t`;
   c696ow_shape C696OW_O; c696ow_shape C696OW_A; c696ow_shape C696OW_W;
   c696ow_equiv C696OW_O 1; c696ow_equiv C696OW_A 256; c696ow_equiv C696OW_W 4096;
   mk_neg (c696ck_oin 1 `&1` `&1`); mk_neg (c696ck_oin 256 `&2` `&2`); c696ck_oin 256 `&1` `&2`];;
let C696OW_LHYPS =
  [c696ow_unit C696OW_L; c696ow_pos C696OW_L; `&0 < cL`; `abs sL <= cL`; c696ow_shape C696OW_L;
   c696ow_equiv C696OW_L 2];;

(* the whole argument, with the canonical frame L of owners p 1 as assumed hypotheses *)
let c696ow_core () =
  let ha = ASSUME (list_mk_conj C696OW_HYPS) in
  let [uO; pO; uA; pA; uW; pW; on; an; wn; ws; oS; aS; wS; oE; aE; wE; mc; mcen; west] = CONJUNCTS ha in
  let [uL; pL; lc; can; lS; lE] = map ASSUME C696OW_LHYPS in
  let side = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP
  and sidele = MP (SPECL C696SSP_VARS OO_SIDE_LE) C696SSP_NP in
  let ar = c696ow_arith in
  let sideA = ar [aS; side] `&1 < aA` and sideCap = ar [aS; sidele] `aA <= &1001 / &1000`
  and oSide = ar [oS; side] `&1 < aO` and wSide = ar [wS; side] `&1 < aW`
  and lSide = ar [lS; side] `&1 < aL` in
  let sameOA = ar [oS; aS] `aO:real = aA` and sameAW = ar [aS; wS] `aA:real = aW`
  and sameOL = ar [oS; lS] `aO:real = aL` and sameLW = ar [lS; wS] `aL:real = aW` in
  let oBox = c696ow_box oE C696OW_O 1 and lBox = c696ow_box lE C696OW_L 2
  and wBox = c696ow_box wE C696OW_W 4096 in
  let q = c696ck_q in
  let oMarker = c696ow_to oE (q 0 (`&1`, `&457 / &500`) true)
  and oNear = c696ow_to oE (q 0 (`&28 / &25`, `&1`) true)
  and oFar = c696ow_to oE (q 0 (`&187 / &100`, `&19 / &25`) true)
  and oMissing = c696ow_to oE mc
  and oNext = c696ow_to oE (q 0 (`&2`, `&457 / &500`) false) in
  let lMarker = c696ow_to lE (q 1 (`&457 / &500`, `&1`) true) in
  let lFarOriginal = q 1 (`&19 / &25`, `&187 / &100`) true in
  let lFar = c696ow_to lE lFarOriginal in
  let corner = c696ow_to lE (MP (SPECL C696OW_A (UNDISCH (SPEC_ALL C696CK_LEFT_CORNER)))
    (end_itlist CONJ [uA; pA; an; aS; aE; mcen])) in
  let wMarker = c696ow_to wE (q 8 (`&457 / &500`, `&2`) true)
  and wPoint = c696ow_to wE (q 8 (`&1`, `&113 / &50`) true)
  and wHigh = c696ow_to wE (q 8 (`&1`, `&12 / &5`) true)
  and wMissingTop = c696ow_to wE (q 8 (`&457 / &500`, `&3`) false)
  and wMissingNW = c696ow_to wE (q 8 (`&33 / &20`, `&47 / &20`) false) in
  let wMissingFar =
    let d = SPECL [`&19 / &25`; `&187 / &100`]
      (REWRITE_RULE[ldisj] (MP (SPEC_ALL (oo_apart `c696ssp_family` 4096 2)) C696SSP_HH)) in
    let fw = lhand (rand (concl d)) in
    c696ow_to wE (NOT_INTRO (DISCH fw (MP (NOT_ELIM d) (CONJ (ASSUME fw) lFarOriginal)))) in
  let aMarker = c696ow_to aE (q 6 (`&33 / &20`, `&33 / &20`) true)
  and aD = c696ow_to aE (q 6 (`&2`, `&87 / &50`) true)
  and aEp = c696ow_to aE (q 6 (`&87 / &50`, `&2`) true) in
  let cross = CONJUNCTS (UNDISCH (SPEC_ALL C696CR_CENTRAL_POINTS)) in
  let aLeft = c696ow_to aE (el 3 cross) and aLow = c696ow_to aE (el 2 cross)
  and aWest = c696ow_to aE west in
  let missingNW = c696ow_to aE (q 6 (`&33 / &20`, `&47 / &20`) false)
  and foreignLow = c696ow_to aE (q 6 (`&1`, `&8 / &5`) false) in
  let ab = MATCH_MP C977CC_NORMAL_BOUNDS an and an1 = CONJUNCT1 (REWRITE_RULE[c977cc_normal] an) in
  let cap =
    let hi = ASSUME `&2 * (cA + sA) < uA + aA` in
    let lin th = REWRITE_RULE[linside] th in
    let a22 = EQ_MP (SYM (REWRITE_CONV[linside] (c696ow_in C696OW_A `&2` `&2`)))
      (c696ow_arith [lin aMarker; lin aD; lin aEp; ab; an1; hi]
         (rhs (concl (REWRITE_CONV[linside] (c696ow_in C696OW_A `&2` `&2`))))) in
    let f = MP (NOT_ELIM mcen) (EQ_MP (SPECL [`&2`; `&2`] aE) a22) in
    EQ_MP (REAL_ARITH `~(&2 * (cA + sA) < uA + aA) <=> uA + aA <= &2 * (cA + sA)`) (NOT_INTRO (DISCH (concl hi) f)) in
  let oa = c696ow_ldisj oE C696OW_O 1 aE C696OW_A 256
  and aw = c696ow_ldisj aE C696OW_A 256 wE C696OW_W 4096
  and ol = c696ow_ldisj oE C696OW_O 1 lE C696OW_L 2
  and lw = c696ow_ldisj lE C696OW_L 2 wE C696OW_W 4096 in
  let lower = MP (SPECL (C696OW_A @ C696OW_W @ [`t:real`]) NWTS_LOWER_FACE)
    (end_itlist CONJ [uA; pA; uW; pW; an; wn; ws; sameAW; sideA; cap; aLeft; aLow; aMarker;
                      wMarker; wHigh; wMissingFar; aw]) in
  let top = MP (SPECL (C696OW_W @ [`t:real`]) NWMC_UPPER_FACE)
    (end_itlist CONJ [uW; pW; wn; ws; wSide; wMarker; lower; wMissingNW; wMissingTop]) in
  let northwest = MP (SPECL (C696OW_W @ [`t:real`]) NWMC_UPPER_U)
    (end_itlist CONJ [uW; pW; wn; ws; wSide; wMarker; lower; wMissingNW]) in
  let range = CONJUNCTS (MP (SPECL [`cW:real`; `t:real`; `aW:real`; `vW:real`; `vW + aW`] NWMC_SECTOR)
    (end_itlist CONJ [wn; wSide; REFL `vW + aW`; lower; top])) in
  let oFaces = CONJUNCTS (MP (SPECL C696OW_O C696PC_CORNER_FACES)
    (end_itlist CONJ [on; oSide; oBox; oMarker; oNear; oMissing; oNext])) in
  let bottomFace = REWRITE_RULE[GSYM C696OW_BOUNDARY] (el 4 oFaces) in
  let order = MP (SPECL (C696OW_O @ C696OW_A @ C696OW_W @ [`t:real`]) PCWAO_ANGLE_ORDER)
    (end_itlist CONJ [uO; pO; uA; pA; uW; pW; on; an; wn; ws; sameOA; sameAW; sideA; sideCap;
       oBox; wBox; oMarker; oNear; oFar; oMissing; oNext; aMarker; aD; aLeft; aLow; aWest;
       missingNW; foreignLow; cap; wMarker; wPoint; wMissingTop; wMissingFar; oa; aw]) in
  let data = EQ_MP (SYM (REWR_CONV cwmcy_data (list_mk_comb(`cwmcy_data`, C696OW_O @ C696OW_L @ C696OW_W @ [`t:real`]))))
    (end_itlist CONJ [on; lc; can; wn; ws; lSide; sameOL; sameLW; oBox; lBox; wBox;
       oMarker; oNear; oFar; lMarker; corner; lFar; wMarker; el 2 oFaces; bottomFace;
       northwest; top; MATCH_MP REAL_LT_IMP_LE order;
       MATCH_MP REAL_LT_IMP_LE (el 2 range); MATCH_MP REAL_LT_IMP_LE (el 3 range); ol; lw]) in
  c696wc_fix (MP (SPECL (C696OW_O @ C696OW_L @ C696OW_W @ [`t:real`]) CWMCY_IMPOSSIBLE)
    (end_itlist CONJ [uO; pO; uL; pL; uW; pW; data]));;

(* Lean: frame_excludes *)
let C696OW_FRAME_EXCLUDES =
  let core = c696ow_core () in
  prove
   (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
      list_mk_forall(C696OW_O @ C696OW_A @ C696OW_W @ [`t:real`], mk_imp(list_mk_conj C696OW_HYPS, `false`)))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL (c696ssp_q 2) CLF_CANONICAL_FRAME) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[OO_UNIT]; MATCH_MP_TAC(REAL_ARITH `&1 < l ==> &0 < l`) THEN ASM_MESON_TAC[OO_SIDE]];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C696OW_L THEN STRIP_TAC THEN
    ACCEPT_TAC core);;
