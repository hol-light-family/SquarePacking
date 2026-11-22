(* ========================================================================= *)
(* Phase 2: Compact/Completion/C1092/MPPMMissingBoundaryShallowActual.lean   *)
(* (N12Compact.C1092MPPMMissingBoundaryShallow; Lean header: "Source-only"). *)
(* Literal original Q4/Q9 map for MISSING-BOUNDARY-SHALLOW-ANGLE.            *)
(* Conventions of CP_C1092_MPPMEntrance.ml: owners p i is the OriginalOwners *)
(* 5-tuple at mask EL i c1092wc_code (side l), WallContext p mppm is          *)
(* c1092wc_ctx c1 c2 a b l c1092mppe_mppm.  C, B are cC sC uC vC aC and      *)
(* cB sB uB vB aB; ActualFrames = c1092mbsa_frames, CentralProfile =         *)
(* c1092mbsa_central_profile, Normal = c977cc_normal, Input = c1092mbsg_input,*)
(* shallow = C1092MBSH_SHALLOW, wall_auxiliaries = C1092MPPE_WALL_AUXILIARIES,*)
(* owners_markers = C1092WC_OWNERS_MARKERS, owners_disjoint =                 *)
(* C1092WC_OWNERS_DISJOINT, p.contained = OO_BOX.  Tag C1092MBSA_.           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMMissingBoundaryShallow.ml";;
needs "n12/geometry/CP_C1092_MPPMEntrance.ml";;

(* Lean: ActualFrames (structure) *)
let c1092mbsa_frames = new_definition
 `c1092mbsa_frames c1 c2 a b l (cC:real) (sC:real) (uC:real) (vC:real) (aC:real)
                              (cB:real) (sB:real) (uB:real) (vB:real) (aB:real) <=>
    aC = l /\ aB = l /\
    (forall x y. linside cC sC uC vC aC x y <=>
           linside (ooc c1 c2 a b l (EL 4 c1092wc_code)) (oos c1 c2 a b l (EL 4 c1092wc_code))
                   (oou c1 c2 a b l (EL 4 c1092wc_code)) (oov c1 c2 a b l (EL 4 c1092wc_code)) l
                   (&2 + x) (&2 + y)) /\
    (forall x y. linside cB sB uB vB aB x y <=>
           linside (ooc c1 c2 a b l (EL 9 c1092wc_code)) (oos c1 c2 a b l (EL 9 c1092wc_code))
                   (oou c1 c2 a b l (EL 9 c1092wc_code)) (oov c1 c2 a b l (EL 9 c1092wc_code)) l
                   (&2 + x) (&2 + y))`;;

(* Lean: CentralProfile (structure) *)
let c1092mbsa_central_profile = new_definition
 `c1092mbsa_central_profile (cC:real) sC uC vC aC <=>
    c977cc_normal cC sC /\ &0 < sC /\ --cC - sC / &2 <= uC /\ uC + aC <= &0 /\ vC + aC <= sC`;;

(* Lean: side_gt, side_same (private): the common side l, OO_SIDE *)

(* Lean: marker_point (private), at a literal owner i, marker k (m = EL i c1092wc_code):
   |- linside (owners p i) (marker k)  with hypotheses NPACK, IMAGE *)
let c1092mbsa_marker i k m =
  let lt n b = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral n) (mk_small_numeral b))) in
  let bits = prove(mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral k),
                   mk_comb(`bitset`, mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral i), `c1092wc_code`))),
    REWRITE_TAC(Array.to_list C1092WC_CODE_EL) THEN
    REWRITE_TAC[bitset_bits m; IN_SET_OF_LIST; MEM] THEN CONV_TAC NUM_REDUCE_CONV) in
  let mk = MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                      mk_small_numeral i] C1092WC_OWNERS_MARKERS)
              (CONJ (ASSUME `NPACK c1 c2 a b l`)
                 (CONJ (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`) (lt i 12))) in
  let th = MP (SPEC (mk_small_numeral k) mk) (lt k 16) in
  CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (REWRITE_RULE[MARKER_EXPLICIT; VECTOR_2] (EQ_MP (SYM th) bits));;

let C1092MBSA_MARK_B = c1092mbsa_marker 9 13 8192;;
let C1092MBSA_MARK_K = c1092mbsa_marker 0 0 3;;

let C1092MBSA_HYPS =
  `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
   c1092wc_ctx c1 c2 a b l c1092mppe_mppm /\
   linside (ooc c1 c2 a b l (EL 4 c1092wc_code)) (oos c1 c2 a b l (EL 4 c1092wc_code))
           (oou c1 c2 a b l (EL 4 c1092wc_code)) (oov c1 c2 a b l (EL 4 c1092wc_code)) l (&1) (&8 / &5) /\
   linside (ooc c1 c2 a b l (EL 4 c1092wc_code)) (oos c1 c2 a b l (EL 4 c1092wc_code))
           (oou c1 c2 a b l (EL 4 c1092wc_code)) (oov c1 c2 a b l (EL 4 c1092wc_code)) l (&87 / &50) (&2) /\
   ~linside (ooc c1 c2 a b l (EL 9 c1092wc_code)) (oos c1 c2 a b l (EL 9 c1092wc_code))
            (oou c1 c2 a b l (EL 9 c1092wc_code)) (oov c1 c2 a b l (EL 9 c1092wc_code)) l (&2) (&1) /\
   c1092mbsa_frames c1 c2 a b l cC sC uC vC aC cB sB uB vB aB /\
   c1092mbsa_central_profile cC sC uC vC aC /\
   c977cc_normal cB (--sB) /\ &0 < --sB`;;

let C1092MBSA_ALL = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
  `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

(* Lean: actual_inputs *)
let C1092MBSA_ACTUAL_INPUTS = prove
 (list_mk_forall(C1092MBSA_ALL,
    mk_imp(C1092MBSA_HYPS, `c1092mbsg_input cC sC uC vC aC cB sB uB vB aB`)),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mbsa_frames; c1092mbsa_central_profile] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aC:real = l` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aB:real = l` o concl)) THEN
  REWRITE_TAC[c1092mbsg_input; ldisj] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
            C1092MPPE_WALL_AUXILIARIES) THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `9`; `0`]
            C1092WC_OWNERS_DISJOINT) THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `4`; `9`]
            C1092WC_OWNERS_DISJOINT) THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 `EL 9 c1092wc_code`] OO_BOX) THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE) THEN
  ASM_REWRITE_TAC[ARITH; ldisj; lcont; C1092MBSA_MARK_B; C1092MBSA_MARK_K] THEN
  REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_ASSUM(fun bx ->
           MP_TAC(MATCH_MP bx th))) THEN REAL_ARITH_TAC;
         FIRST_ASSUM(fun th -> if is_forall (concl th) && free_in `EL 0 c1092wc_code` (concl th)
           then MP_TAC (SPECL [`&1`; `&457 / &500`] th) else NO_TAC) THEN
         REWRITE_TAC[C1092MBSA_MARK_K]]);;

(* Lean: actual_shallow *)
let C1092MBSA_ACTUAL_SHALLOW = prove
 (list_mk_forall(C1092MBSA_ALL,
    mk_imp(C1092MBSA_HYPS, `&0 < --sB / cB /\ --sB / cB < &1 / &4`)),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1092MBSA_ACTUAL_INPUTS) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[c1092mbsa_frames; c1092mbsa_central_profile; c977cc_normal] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aC:real = l` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aB:real = l` o concl)) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < cB` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC C1092MBSH_SHALLOW THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`;
                        `uB:real`; `vB:real`; `l:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `cB pow 2 + --sB pow 2 = &1` THEN UNDISCH_TAC `cC pow 2 + sC pow 2 = &1` THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN REAL_ARITH_TAC);;
