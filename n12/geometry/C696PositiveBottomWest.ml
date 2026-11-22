(* ========================================================================= *)
(* Port of Compact/Bridge/C696PositiveBottomWest.lean (namespace N12Compact. *)
(* C696PositiveBottomWest).  (Lean header: "Source only, uncompiled".)       *)
(* Positive bottom frames in the original C696 missing-corner root force the *)
(* central west point, and then both signs of the wall frame are excluded.   *)
(* Conventions of C696CornerReach.ml / C696OwnedWestCorner.ml: owners p 0,   *)
(* 1, 6, 8 are the owners of masks 1, 2, 256, 4096; the frames O, A, W are   *)
(* cO sO uO vO aO etc. with unit normal and positive side (OpenSquare        *)
(* fields); Normal is c977cc_normal; shapes are aO = l etc.  The canonical   *)
(* frames L (of owners p 1) and W (of owners p 8) come from                  *)
(* CLF_CANONICAL_FRAME.  Used: PositiveCentralPositiveLeftWest.west          *)
(* (PCPLW_WEST), PositiveCentralNegativeLeft.west (PCNL_WEST),               *)
(* C696CornerReach.left_corner (C696CK_LEFT_CORNER), C696NegativeCentral.    *)
(* positive_frame_of_missing_center (C696NC_POSITIVE_FRAME_OF_MISSING_CENTER), *)
(* C696PositiveWallOwnedWest.frame_excludes (C696PW_FRAME_EXCLUDES, wall     *)
(* index 0), C696OwnedWestCorner.frame_excludes (C696OW_FRAME_EXCLUDES).     *)
(* Tag C696PBW_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/C696CornerReach.ml";;
needs "n12/geometry/C696NegativeCentral.ml";;
needs "n12/geometry/C696PositiveWallOwnedWest.ml";;
needs "n12/geometry/C696OwnedWestCorner.ml";;
needs "n12/geometry/PositiveCentralNegativeLeft.ml";;
needs "n12/geometry/PositiveCentralPositiveLeftWest.ml";;

(* Lean: apart (private) is oo_apart *)

let C696PBW_NEG_NORMAL = prove
 (`forall c s. ~(&0 <= s) /\ abs s <= c /\ c * c + s * s = &1 ==> c977cc_normal c (--s)`,
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REAL_ARITH_TAC);;

let C696PBW_POS_NORMAL = prove
 (`forall c s. &0 < s /\ s <= c /\ c * c + s * s = &1 ==> c977cc_normal c s`,
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REAL_ARITH_TAC);;

let C696PBW_O = C696OW_O and C696PBW_A = C696OW_A and C696PBW_L = C696OW_L and C696PBW_W = C696OW_W;;

let C696PBW_FW_HYPS =
  [c696ow_unit C696PBW_O; c696ow_pos C696PBW_O; c696ow_unit C696PBW_A; c696ow_pos C696PBW_A;
   `c977cc_normal cO sO`; `c977cc_normal cA sA`;
   c696ow_shape C696PBW_O; c696ow_shape C696PBW_A;
   c696ow_equiv C696PBW_O 1; c696ow_equiv C696PBW_A 256;
   mk_neg (c696ck_oin 1 `&1` `&1`); mk_neg (c696ck_oin 256 `&2` `&2`)];;

(* frame_west with the canonical frame L of owners p 1 as assumed hypotheses *)
let c696pbw_fw_core () =
  let ha = ASSUME (list_mk_conj C696PBW_FW_HYPS) in
  let [uO; pO; uA; pA; on; an; oS; aS; oE; aE; mc; mcen] = CONJUNCTS ha in
  let [uL; pL; lc; can; lS; lE] = map ASSUME C696OW_LHYPS in
  let side = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP and sidele = MP (SPECL C696SSP_VARS OO_SIDE_LE) C696SSP_NP in
  let ar = c696ow_arith in
  let sideA = ar [aS; side] `&1 < aA` and small = ar [aS; sidele] `aA <= &1001 / &1000` in
  let sameO = ar [oS; aS] `aO:real = aA` and sameL = ar [lS; aS] `aL:real = aA` in
  let oBox = c696ow_box oE C696PBW_O 1 and lBox = c696ow_box lE C696PBW_L 2 in
  let q = c696ck_q in
  let oMarker = c696ow_to oE (q 0 (`&1`, `&457 / &500`) true) and oNear = c696ow_to oE (q 0 (`&28 / &25`, `&1`) true) and oFar = c696ow_to oE (q 0 (`&187 / &100`, `&19 / &25`) true) and oMissingCorner = c696ow_to oE mc and oMissingMarker = c696ow_to oE (q 0 (`&2`, `&457 / &500`) false) in
  let lCorner = c696ow_to lE (MP (SPECL C696PBW_A (UNDISCH (SPEC_ALL C696CK_LEFT_CORNER)))
    (end_itlist CONJ [uA; pA; an; aS; aE; mcen])) in
  let lNear = c696ow_to lE (q 1 (`&1`, `&28 / &25`) true) and lFar = c696ow_to lE (q 1 (`&19 / &25`, `&187 / &100`) true) in
  let aMarker = c696ow_to aE (q 6 (`&33 / &20`, `&33 / &20`) true) and aD = c696ow_to aE (q 6 (`&2`, `&87 / &50`) true) and aEp = c696ow_to aE (q 6 (`&87 / &50`, `&2`) true) in
  let cross = CONJUNCTS (UNDISCH (SPEC_ALL C696CR_CENTRAL_POINTS)) in
  let aLeft = c696ow_to aE (el 3 cross) and aLow = c696ow_to aE (el 2 cross) in
  let missingNW = c696ow_to aE (q 6 (`&33 / &20`, `&47 / &20`) false) and foreignLow = c696ow_to aE (q 6 (`&1`, `&8 / &5`) false) in
  let ab = MATCH_MP C977CC_NORMAL_BOUNDS an and an1 = CONJUNCT1 (REWRITE_RULE[c977cc_normal] an) in
  let cap =
    let hi = ASSUME `&2 * (cA + sA) < uA + aA` in
    let lin th = REWRITE_RULE[linside] th in
    let a22 = EQ_MP (SYM (REWRITE_CONV[linside] (c696ow_in C696PBW_A `&2` `&2`)))
      (c696ow_arith [lin aMarker; lin aD; lin aEp; ab; an1; hi]
         (rhs (concl (REWRITE_CONV[linside] (c696ow_in C696PBW_A `&2` `&2`))))) in
    let f = MP (NOT_ELIM mcen) (EQ_MP (SPECL [`&2`; `&2`] aE) a22) in
    EQ_MP (REAL_ARITH `~(&2 * (cA + sA) < uA + aA) <=> uA + aA <= &2 * (cA + sA)`)
      (NOT_INTRO (DISCH (concl hi) f)) in
  let oa = c696ow_ldisj oE C696PBW_O 1 aE C696PBW_A 256 and ol = c696ow_ldisj oE C696PBW_O 1 lE C696PBW_L 2 and la = c696ow_ldisj lE C696PBW_L 2 aE C696PBW_A 256 in
  let common = [oBox; lBox; oMarker; oNear; oFar; oMissingCorner; oMissingMarker; lCorner; lNear; lFar;
                aMarker; aD; aEp; aLeft; aLow; cap; missingNW; foreignLow; oa; ol; la] in
  let nnt = `&0 <= sL` in
  let pos_case =
    let ln = MP (SPECL [`cL:real`; `sL:real`] C696PW_NORMAL_OF_CANONICAL)
                (end_itlist CONJ [ASSUME nnt; can; uL]) in
    MP (SPECL (C696PBW_O @ C696PBW_L @ C696PBW_A) PCPLW_WEST)
       (end_itlist CONJ ([uO; pO; uL; pL; uA; pA; on; ln; an; sameO; sameL; sideA] @ common)) in
  let neg_case =
    let nn = ASSUME (mk_neg nnt) in
    let ln = MP (SPECL [`cL:real`; `sL:real`] C696PBW_NEG_NORMAL) (end_itlist CONJ [nn; can; uL]) in
    let negative = MP (REAL_ARITH `~(&0 <= sL) ==> &0 < --sL`) nn in
    MP (SPECL (C696PBW_O @ C696PBW_L @ C696PBW_A @ [`--sL:real`]) PCNL_WEST)
       (end_itlist CONJ ([on; ln; SYM (SPEC `sL:real` REAL_NEG_NEG); negative; an; sameO; sameL;
                          sideA; small] @ common)) in
  let west = DISJ_CASES (SPEC nnt EXCLUDED_MIDDLE) pos_case neg_case in
  c696wc_fix (EQ_MP (SPECL [`&1`; `&2`] aE) west);;

(* Lean: frame_west *)
let C696PBW_FRAME_WEST =
  let core = c696pbw_fw_core () in
  prove
   (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
      list_mk_forall(C696PBW_O @ C696PBW_A, mk_imp(list_mk_conj C696PBW_FW_HYPS, c696ck_oin 256 `&1` `&2`)))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL (c696ssp_q 2) CLF_CANONICAL_FRAME) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[OO_UNIT]; MATCH_MP_TAC(REAL_ARITH `&1 < l ==> &0 < l`) THEN ASM_MESON_TAC[OO_SIDE]];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C696PBW_L THEN STRIP_TAC THEN
    ACCEPT_TAC core);;

let C696PBW_WEST_HYPS =
  [c696ow_unit C696PBW_O; c696ow_pos C696PBW_O; `c977cc_normal cO sO`; c696ow_shape C696PBW_O;
   c696ow_equiv C696PBW_O 1; mk_neg (c696ck_oin 1 `&1` `&1`); mk_neg (c696ck_oin 256 `&2` `&2`)];;

(* the central frame A of C696NC_POSITIVE_FRAME_OF_MISSING_CENTER, as a tactic *)
let C696PBW_CENTRAL_TAC =
  MP_TAC(SPEC_ALL C696NC_POSITIVE_FRAME_OF_MISSING_CENTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C696PBW_A THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal cA sA` ASSUME_TAC THENL
   [MATCH_MP_TAC C696PBW_POS_NORMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (c696ck_oin 256 `&1` `&2`) ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL C696PBW_FRAME_WEST) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL (C696PBW_O @ C696PBW_A)) THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(* Lean: west *)
let C696PBW_WEST = prove
 (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
    list_mk_forall(C696PBW_O, mk_imp(list_mk_conj C696PBW_WEST_HYPS, c696ck_oin 256 `&1` `&2`)))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  C696PBW_CENTRAL_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: positive_wall_excludes *)
let C696PBW_POSITIVE_WALL_EXCLUDES =
  let pw0 = CONJUNCT1 (UNDISCH (SPEC_ALL C696PW_FRAME_EXCLUDES)) in
  prove
   (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
      list_mk_forall(C696PBW_O @ C696PBW_W, mk_imp(list_mk_conj
        [c696ow_unit C696PBW_O; c696ow_pos C696PBW_O; c696ow_unit C696PBW_W; c696ow_pos C696PBW_W;
         `c977cc_normal cO sO`; `c977cc_normal cW sW`; c696ow_shape C696PBW_O; c696ow_shape C696PBW_W;
         c696ow_equiv C696PBW_O 1; c696ow_equiv C696PBW_W 4096;
         mk_neg (c696ck_oin 1 `&1` `&1`); mk_neg (c696ck_oin 256 `&2` `&2`)], `false`)))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (c696ck_oin 256 `&1` `&2`) ASSUME_TAC THENL
     [MP_TAC(SPEC_ALL C696PBW_WEST) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL C696PBW_O) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(DISCH C696SSP_HYP pw0) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL C696PBW_W) THEN ASM_REWRITE_TAC[]);;

(* Lean: frame_excludes *)
let C696PBW_FRAME_EXCLUDES =
  let pw0 = DISCH C696SSP_HYP (CONJUNCT1 (UNDISCH (SPEC_ALL C696PW_FRAME_EXCLUDES))) in
  prove
   (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
      list_mk_forall(C696PBW_O, mk_imp(list_mk_conj C696PBW_WEST_HYPS, `false`)))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    C696PBW_CENTRAL_TAC THEN
    MP_TAC(SPECL (c696ssp_q 4096) CLF_CANONICAL_FRAME) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[OO_UNIT]; MATCH_MP_TAC(REAL_ARITH `&1 < l ==> &0 < l`) THEN ASM_MESON_TAC[OO_SIDE]];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C696PBW_W THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 <= sW` THENL
     [SUBGOAL_THEN `c977cc_normal cW sW` ASSUME_TAC THENL
       [MATCH_MP_TAC C696PW_NORMAL_OF_CANONICAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC pw0 THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL C696PBW_W) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `c977cc_normal cW (--sW)` ASSUME_TAC THENL
       [MATCH_MP_TAC C696PBW_NEG_NORMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC_ALL C696OW_FRAME_EXCLUDES) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL (C696PBW_O @ C696PBW_A @ C696PBW_W @ [`--sW:real`])) THEN
      ASM_REWRITE_TAC[REAL_NEG_NEG]]);;

(* Lean: canonical_sine_negative *)
let C696PBW_CANONICAL_SINE_NEGATIVE = prove
 (list_mk_forall(C696SSP_VARS, mk_imp(C696SSP_HYP,
    list_mk_forall(C696PBW_O, mk_imp(list_mk_conj
      [c696ow_unit C696PBW_O; c696ow_pos C696PBW_O; `abs sO <= cO`; c696ow_shape C696PBW_O;
       c696ow_equiv C696PBW_O 1; mk_neg (c696ck_oin 1 `&1` `&1`); mk_neg (c696ck_oin 256 `&2` `&2`)],
      `sO < &0`)))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c977cc_normal cO sO` ASSUME_TAC THENL
   [MATCH_MP_TAC C696PW_NORMAL_OF_CANONICAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL C696PBW_FRAME_EXCLUDES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL C696PBW_O) THEN ASM_REWRITE_TAC[]);;
