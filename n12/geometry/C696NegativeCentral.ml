(* ========================================================================= *)
(* Port of Compact/Bridge/C696NegativeCentral.lean (namespace N12Compact.    *)
(* C696NegativeCentral).  Original-packing entrance to the negative-central  *)
(* sector.  Conventions of C696CornerReach.ml (A = cA sA uA vA aA with unit  *)
(* normal and positive side; Normal = c977cc_normal; shape aA = l).          *)
(* SouthwestNegativeCorner.point = SNC_POINT; ClosedFrames.canonical_frame = *)
(* CLF_CANONICAL_FRAME.  Tag C696NC_.                                        *)
(* ========================================================================= *)

needs "n12/geometry/C696CornerReach.ml";;
needs "n12/geometry/SouthwestNegativeCorner.ml";;

(* Lean: apart / inside (private) are oo_apart / c696ssp_inside *)

(* Lean: center_of_negative_frame *)
let C696NC_CORNER = mk_neg (c696ck_oin 1 `&1` `&1`);;
let C696NC_CENTER_OF_NEGATIVE_FRAME =
  let hyps = [`cA * cA + sA * sA = &1`; `&0 < aA`; `sA = --TT`; `c977cc_normal cA TT`; `aA:real = l`;
              c696ck_equiv 256] in
  let ha = ASSUME (list_mk_conj hyps) in
  let [u; pos; hs; nrm; shape; eqv] = CONJUNCTS ha in
  let side = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP in
  let cp = UNDISCH (SPEC_ALL C696CR_CENTRAL_POINTS) in
  let anew = c696ck_toa eqv (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 cp))) in
  let reach = MP (SPECL (c696ssp_q 1 @ C696CK_A @ c696ssp_q 2 @ [`TT:real`]) SNC_POINT)
    (end_itlist CONJ
      [MP (SPECL (C696SSP_VARS @ [`1`]) OO_UNIT) C696SSP_NP; hs; nrm; SYM shape;
       MP (REAL_ARITH `aA:real = l /\ &1 < l ==> &1 < aA`) (CONJ shape side);
       MP (SPECL (C696SSP_VARS @ [`1`]) OO_BOX) C696SSP_NP;
       c696ck_q 0 (`&1`, `&457 / &500`) true; c696ck_q 0 (`&28 / &25`, `&1`) true;
       c696ck_q 0 (`&187 / &100`, `&19 / &25`) true; ASSUME C696NC_CORNER;
       c696ck_q 0 (`&2`, `&457 / &500`) false;
       c696ck_toa eqv (c696ck_q 6 (`&33 / &20`, `&33 / &20`) true);
       c696ck_toa eqv (c696ck_q 6 (`&2`, `&87 / &50`) true);
       c696ck_toa eqv (c696ck_q 6 (`&87 / &50`, `&2`) true); anew;
       c696ck_q 1 (`&1`, `&28 / &25`) true; c696ck_q 1 (`&1`, `&87 / &50`) true;
       c696ck_ldisj eqv 1 256 false; c696ck_ldisj eqv 256 2 true]) in
  let th = EQ_MP (SPECL [`&2`; `&2`] eqv) reach in
  GENL C696SSP_VARS (DISCH (mk_conj(C696SSP_HYP, C696NC_CORNER))
    (PROVE_HYP (CONJUNCT1 (ASSUME (mk_conj(C696SSP_HYP, C696NC_CORNER))))
      (PROVE_HYP (CONJUNCT2 (ASSUME (mk_conj(C696SSP_HYP, C696NC_CORNER))))
        (c696wc_fix (GENL (C696CK_A @ [`TT:real`]) (DISCH (concl ha) th))))));;

(* Lean: positive_frame_of_missing_center *)
let C696NC_POSITIVE_FRAME_OF_MISSING_CENTER = prove
 (list_mk_forall(C696SSP_VARS, mk_imp(list_mk_conj [C696SSP_HYP; C696NC_CORNER; mk_neg (c696ck_oin 256 `&2` `&2`)],
    list_mk_exists(C696CK_A, list_mk_conj
      [`cA * cA + sA * sA = &1`; `&0 < aA`; `&0 < cA`; `&0 < sA`; `sA <= cA`; `aA:real = l`;
       c696ck_equiv 256; mk_neg (c696ck_ain `&2` `&2`)]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (c696ssp_q 256) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[OO_UNIT]; MATCH_MP_TAC(REAL_ARITH `&1 < l ==> &0 < l`) THEN ASM_MESON_TAC[OO_SIDE]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC C696CK_A THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 < sA` THENL
   [MAP_EVERY EXISTS_TAC C696CK_A THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    MP_TAC(SPEC_ALL C696NC_CENTER_OF_NEGATIVE_FRAME) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL (C696CK_A @ [`--sA:real`])) THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG; c977cc_normal; REAL_POW_2] THEN
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    UNDISCH_TAC `cA * cA + sA * sA = &1` THEN REAL_ARITH_TAC]);;
