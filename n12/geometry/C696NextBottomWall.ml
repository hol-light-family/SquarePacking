(* ========================================================================= *)
(* Port of Compact/Bridge/C696NextBottomWall.lean (namespace N12Compact.     *)
(* C696NextBottomWall).  (Lean header: "Source only, uncompiled".)           *)
(* The original C696 missing-corner / missing-center / missing-west branch   *)
(* is impossible.  Conventions of C696CornerReach.ml / C696OwnedWestCorner.ml:*)
(* owners p 0, 6, 9 are the owners of masks 1, 256, 8192; the frames O, A, D *)
(* are cO sO uO vO aO etc. with unit normal and positive side (OpenSquare    *)
(* fields); Normal is c977cc_normal; O.s = -t is sO = --t; shapes are        *)
(* aO = l etc.  The private transpose of D is the tuple cD (--sD) vD uD aD   *)
(* (C696NBW_INSIDE_TRANSPOSE).  Used: NegativeBottomNextWall.impossible      *)
(* (NBNW_IMPOSSIBLE), NegativeBottomInnerWall.impossible (NBIW_IMPOSSIBLE),  *)
(* PositiveWallPositiveLeft.cuts (PWPL_CUTS, Cuts = pwpl_cuts),              *)
(* C696PositiveWallOwnedWest.frame_point (C696PW_FRAME_POINT, frame 1),      *)
(* C696PositiveBottomWest.canonical_sine_negative                            *)
(* (C696PBW_CANONICAL_SINE_NEGATIVE), ClosedFrames.canonical_frame           *)
(* (CLF_CANONICAL_FRAME).  Tag C696NBW_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/C696PositiveBottomWest.ml";;
needs "n12/geometry/PositiveWallPositiveLeft.ml";;
needs "n12/geometry/NegativeBottomNextWall.ml";;
needs "n12/geometry/NegativeBottomInnerWall.ml";;
needs "n12/geometry/C696PositiveWallOwnedWest.ml";;

(* Lean: transpose (private def) is the tuple c (--s) v u a *)
(* Lean: inside_transpose (private) *)
let C696NBW_INSIDE_TRANSPOSE = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: apart (private) is oo_apart *)

let C696NBW_O = C696OW_O and C696NBW_A = C696OW_A and C696NBW_D = c696ow_sq "D";;

let C696NBW_OHYPS =
  [c696ow_unit C696NBW_O; c696ow_pos C696NBW_O; `sO = --t`; `c977cc_normal cO t`; `t <= &1 / &5`;
   c696ow_shape C696NBW_O; c696ow_equiv C696NBW_O 1; mk_neg (c696ck_oin 1 `&1` `&1`)];;
let C696NBW_DHYPS =
  [c696ow_unit C696NBW_D; c696ow_pos C696NBW_D; `abs sD <= cD`; c696ow_shape C696NBW_D;
   c696ow_equiv C696NBW_D 8192];;

(* the common D-sign argument of excludes_of_small_bottom and frame_excludes *)
let c696nbw_core () =
  let ha = ASSUME (list_mk_conj (C696NBW_OHYPS @ C696NBW_DHYPS)) in
  let [uO; pO; os; on; small; oS; oE; mc; uD; pD; can; dS; dE] = CONJUNCTS ha in
  let side = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP in
  let ar = c696ow_arith in
  let sameOD = ar [oS; dS] `aO:real = aD` and sideO = ar [oS; side] `&1 < aO` in
  let oBox = c696ow_box oE C696NBW_O 1 and dBox = c696ow_box dE C696NBW_D 8192 in
  let q = c696ck_q in
  let oMarker = c696ow_to oE (q 0 (`&1`, `&457 / &500`) true) in
  let oNear = c696ow_to oE (q 0 (`&28 / &25`, `&1`) true) in
  let oMiddle = c696ow_to oE (q 0 (`&87 / &50`, `&1`) true) in
  let oFar = c696ow_to oE (q 0 (`&187 / &100`, `&19 / &25`) true) in
  let oCorner = c696ow_to oE mc in
  let dMarker = c696ow_to dE (q 9 (`&2`, `&457 / &500`) true) in
  let dMissing = c696ow_to dE (q 9 (`&3`, `&457 / &500`) false) in
  let od = c696ow_ldisj oE C696NBW_O 1 dE C696NBW_D 8192 in
  let nnt = `&0 <= sD` in
  let pos_case =
    let dn = MP (SPECL [`cD:real`; `sD:real`] C696PW_NORMAL_OF_CANONICAL)
                (end_itlist CONJ [ASSUME nnt; can; uD]) in
    MP (SPECL (C696NBW_O @ C696NBW_D @ [`t:real`]) NBNW_IMPOSSIBLE)
       (end_itlist CONJ [uO; uD; pD; os; on; dn; small; sameOD; sideO; oBox; dBox;
                         oMarker; oNear; oMiddle; oFar; oCorner; dMarker; dMissing; od]) in
  let neg_case =
    let nn = ASSUME (mk_neg nnt) in
    let dn = MP (SPECL [`cD:real`; `sD:real`] C696PBW_NEG_NORMAL) (end_itlist CONJ [nn; can; uD]) in
    let ds = SYM (SPEC `sD:real` REAL_NEG_NEG) in
    let tr = [`cD:real`; `--sD:real`; `vD:real`; `uD:real`; `aD:real`] in
    let fp = el 1 (CONJUNCTS (UNDISCH (SPEC_ALL C696PW_FRAME_POINT))) in
    let fhyps = lhand (snd (strip_forall (concl fp))) in
    let teq = el 4 (conjuncts (vsubst (zip tr C696PW_W) fhyps)) in
    let unitT = MP (REAL_ARITH (mk_imp(concl uD, el 0 (conjuncts (vsubst (zip tr C696PW_W) fhyps))))) uD in
    let tE = TAC_PROOF(([], teq),
      REWRITE_TAC[C696NBW_INSIDE_TRANSPOSE; LINSIDE_PULLSW; dE]) in
    let pt = MP (SPECL tr fp) (end_itlist CONJ [unitT; pD; dn; dS; tE]) in
    let inner = EQ_MP (SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `&1`; `&2`]
                         C696NBW_INSIDE_TRANSPOSE) pt in
    MP (SPECL (C696NBW_O @ C696NBW_D @ [`t:real`; `--sD:real`]) NBIW_IMPOSSIBLE)
       (end_itlist CONJ [uO; uD; pD; os; ds; on; dn; small; sameOD; sideO; oBox;
                         oMarker; oNear; oMiddle; oFar; oCorner; dMarker; inner; od]) in
  c696wc_fix (DISJ_CASES (SPEC nnt EXCLUDED_MIDDLE) pos_case neg_case);;

let C696NBW_CORE =
  let th = c696nbw_core () in
  GENL C696SSP_VARS (DISCH C696SSP_HYP
    (GENL (C696NBW_O @ C696NBW_D @ [`t:real`])
      (DISCH (list_mk_conj (C696NBW_OHYPS @ C696NBW_DHYPS)) th)));;

let C696NBW_CANONICAL_TAC m sq =
  MP_TAC(SPECL (c696ssp_q m) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[OO_UNIT]; MATCH_MP_TAC(REAL_ARITH `&1 < l ==> &0 < l`) THEN ASM_MESON_TAC[OO_SIDE]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC sq THEN STRIP_TAC;;

(* Lean: excludes_of_small_bottom *)
let C696NBW_EXCLUDES_OF_SMALL_BOTTOM = prove
 (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
    list_mk_forall(C696NBW_O @ [`t:real`], mk_imp(list_mk_conj C696NBW_OHYPS, `false`)))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  C696NBW_CANONICAL_TAC 8192 C696NBW_D THEN
  MP_TAC(SPEC_ALL C696NBW_CORE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL (C696NBW_O @ C696NBW_D @ [`t:real`])) THEN ASM_REWRITE_TAC[]);;

let C696NBW_FE_HYPS =
  C696NBW_DHYPS @ [mk_neg (c696ck_oin 1 `&1` `&1`); mk_neg (c696ck_oin 256 `&2` `&2`);
                   mk_neg (c696ck_oin 256 `&1` `&2`)];;
let C696NBW_COHYPS =
  [c696ow_unit C696NBW_O; c696ow_pos C696NBW_O; `&0 < cO`; `abs sO <= cO`; c696ow_shape C696NBW_O;
   c696ow_equiv C696NBW_O 1];;
let C696NBW_AHYPS =
  [c696ow_unit C696NBW_A; c696ow_pos C696NBW_A; `&0 < cA`; `&0 < sA`; `sA <= cA`; c696ow_shape C696NBW_A;
   c696ow_equiv C696NBW_A 256; mk_neg (c696ow_in C696NBW_A `&2` `&2`)];;

(* frame_excludes with the canonical frame O and the central frame A as assumed hypotheses *)
let c696nbw_fe_core () =
  let hd = ASSUME (list_mk_conj C696NBW_FE_HYPS) in
  let [uD; pD; can; dS; dE; mc; mcen; mwest] = CONJUNCTS hd in
  let [uO; pO; _; oCan; oS; oE] = map ASSUME C696NBW_COHYPS in
  let [uA; pA; _; aPos; aOrd; aS; aE; _] = map ASSUME C696NBW_AHYPS in
  let negative = MP (SPECL C696NBW_O (UNDISCH (SPEC_ALL C696PBW_CANONICAL_SINE_NEGATIVE)))
    (end_itlist CONJ [uO; pO; oCan; oS; oE; mc; mcen]) in
  let nn = MP (REAL_ARITH `sO < &0 ==> ~(&0 <= sO)`) negative in
  let on = MP (SPECL [`cO:real`; `sO:real`] C696PBW_NEG_NORMAL) (end_itlist CONJ [nn; oCan; uO]) in
  let os = SYM (SPEC `sO:real` REAL_NEG_NEG) in
  let an = MP (SPECL [`cA:real`; `sA:real`] C696PBW_POS_NORMAL) (end_itlist CONJ [aPos; aOrd; uA]) in
  let side = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP in
  let ar = c696ow_arith in
  let sameOA = ar [oS; aS] `aO:real = aA` and sideA = ar [aS; side] `&1 < aA` in
  let oBox = c696ow_box oE C696NBW_O 1 in
  let q = c696ck_q in
  let oMarker = c696ow_to oE (q 0 (`&1`, `&457 / &500`) true) in
  let oNear = c696ow_to oE (q 0 (`&28 / &25`, `&1`) true) in
  let oFar = c696ow_to oE (q 0 (`&187 / &100`, `&19 / &25`) true) in
  let oCorner = c696ow_to oE mc in
  let oMissing = c696ow_to oE (q 0 (`&2`, `&457 / &500`) false) in
  let aMarker = c696ow_to aE (q 6 (`&33 / &20`, `&33 / &20`) true) in
  let aD = c696ow_to aE (q 6 (`&2`, `&87 / &50`) true) in
  let aEp = c696ow_to aE (q 6 (`&87 / &50`, `&2`) true) in
  let cross = CONJUNCTS (UNDISCH (SPEC_ALL C696CR_CENTRAL_POINTS)) in
  let aLeft = c696ow_to aE (el 3 cross) and aLow = c696ow_to aE (el 2 cross) in
  let aMissing = c696ow_to aE mwest in
  let aMissingNW = c696ow_to aE (q 6 (`&33 / &20`, `&47 / &20`) false) in
  let aForeignLow = c696ow_to aE (q 6 (`&1`, `&8 / &5`) false) in
  let ab = MATCH_MP C977CC_NORMAL_BOUNDS an and an1 = CONJUNCT1 (REWRITE_RULE[c977cc_normal] an) in
  let cap =
    let hi = ASSUME `&2 * (cA + sA) < uA + aA` in
    let lin th = REWRITE_RULE[linside] th in
    let a22 = EQ_MP (SYM (REWRITE_CONV[linside] (c696ow_in C696NBW_A `&2` `&2`)))
      (c696ow_arith [lin aMarker; lin aD; lin aEp; ab; an1; hi]
         (rhs (concl (REWRITE_CONV[linside] (c696ow_in C696NBW_A `&2` `&2`))))) in
    let f = MP (NOT_ELIM mcen) (EQ_MP (SPECL [`&2`; `&2`] aE) a22) in
    EQ_MP (REAL_ARITH `~(&2 * (cA + sA) < uA + aA) <=> uA + aA <= &2 * (cA + sA)`)
      (NOT_INTRO (DISCH (concl hi) f)) in
  let oa = c696ow_ldisj oE C696NBW_O 1 aE C696NBW_A 256 in
  let cuts = MP (SPECL (C696NBW_O @ C696NBW_A @ [`--sO:real`]) PWPL_CUTS)
    (end_itlist CONJ [uO; pO; uA; pA; os; on; an; sameOA; sideA; oBox; oMarker; oNear; oFar;
                      oCorner; oMissing; aMarker; aD; aLeft; aLow; cap; aMissing; aMissingNW;
                      aForeignLow; oa]) in
  let small = MP (REAL_ARITH `--sO < &1 / &5 ==> --sO <= &1 / &5`)
                 (CONJUNCT1 (CONJUNCT2 (REWRITE_RULE[pwpl_cuts] cuts))) in
  let core = MP (SPECL (C696NBW_O @ C696NBW_D @ [`--sO:real`]) (UNDISCH (SPEC_ALL C696NBW_CORE)))
    (end_itlist CONJ [uO; pO; os; on; small; oS; oE; mc; uD; pD; can; dS; dE]) in
  c696wc_fix core;;

(* Lean: frame_excludes *)
let C696NBW_FRAME_EXCLUDES =
  let core = c696nbw_fe_core () in
  prove
   (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
      list_mk_forall(C696NBW_D, mk_imp(list_mk_conj C696NBW_FE_HYPS, `false`)))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    C696NBW_CANONICAL_TAC 1 C696NBW_O THEN
    MP_TAC(SPEC_ALL C696NC_POSITIVE_FRAME_OF_MISSING_CENTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC C696NBW_A THEN STRIP_TAC THEN
    ACCEPT_TAC core);;

(* Lean: missing_west *)
let C696NBW_MISSING_WEST = prove
 (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
    mk_imp(list_mk_conj [mk_neg (c696ck_oin 1 `&1` `&1`); mk_neg (c696ck_oin 256 `&2` `&2`);
                         mk_neg (c696ck_oin 256 `&1` `&2`)], `false`))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  C696NBW_CANONICAL_TAC 8192 C696NBW_D THEN
  MP_TAC(SPEC_ALL C696NBW_FRAME_EXCLUDES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL C696NBW_D) THEN ASM_REWRITE_TAC[]);;

(* Lean: canonical_sine_negative *)
let C696NBW_CANONICAL_SINE_NEGATIVE = prove
 (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
    list_mk_forall(C696NBW_D, mk_imp(list_mk_conj C696NBW_FE_HYPS, `sD < &0`)))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  MP_TAC(SPEC_ALL C696NBW_FRAME_EXCLUDES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL C696NBW_D) THEN ASM_REWRITE_TAC[]);;
