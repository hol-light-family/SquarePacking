(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ContinuousCenter.lean         *)
(* (N12Compact.Completion.OtherCases.C1089.ContinuousCenter).               *)
(* C1089-CONTINUOUS-REDUCTION Theorem 3 with all actual sources.            *)
(* The chart R := translate (pullX W) 2 (-2) of W = (c, s, u, v, a) is the   *)
(* 5-tuple (--c, s, u - &2 * c + &2 * s, --v - a - &2 * s - &2 * c, a),      *)
(* with R.Inside x y <=> W.Inside (2 - x) (y - 2) (C1089CC_CHART).          *)
(* WallSignChord.chord: WSC_CHORD; ContinuousOrigin.right_origin_of_points: *)
(* OC1089CO_RIGHT_ORIGIN_OF_POINTS; WallProfile.vertical_owned:             *)
(* OCWPVG_VERTICAL_OWNED; ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME;*)
(* C1092InwardBarCenter.point: C1092IBC_POINT; ContinuousAnchorCenter.point:*)
(* C1089CAC_POINT; ContinuousNegative.impossible: OCCN_IMPOSSIBLE.          *)
(* The OpenSquare invariants are explicit hypotheses.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousAnchorCenter.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousOrigin.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousNegative.ml";;
needs "n12/geometry/CP_C1092_InwardBarCenter.ml";;
needs "n12/geometry/WallSignChord.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: Input (structure) *)
let c1089cc_input = new_definition
 `c1089cc_input (cC:real) (sC:real) (uC:real) (vC:real) (aC:real)
                (cW:real) (sW:real) (uW:real) (vW:real) (aW:real)
                (cB:real) (sB:real) (uB:real) (vB:real) (aB:real)
                (cK:real) (sK:real) (uK:real) (vK:real) (aK:real) <=>
    &1 < aC /\ aC = aW /\ aC = aB /\ aC = aK /\
    ldisj cC sC uC vC aC cW sW uW vW aW /\
    ldisj cC sC uC vC aC cB sB uB vB aB /\
    ldisj cC sC uC vC aC cK sK uK vK aK /\
    ldisj cW sW uW vW aW cB sB uB vB aB /\
    ldisj cW sW uW vW aW cK sK uK vK aK /\
    ldisj cB sB uB vB aB cK sK uK vK aK /\
    linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
    linside cC sC uC vC aC (&0) (&13 / &50) /\
    linside cC sC uC vC aC (&13 / &50) (&0) /\
    ~linside cC sC uC vC aC (--(&7) / &20) (&7 / &20) /\
    linside cW sW uW vW aW (&543 / &500) (&0) /\
    linside cW sW uW vW aW (&1) (&13 / &50) /\
    (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
    &0 <= lcy cW sW uW vW aW /\
    linside cB sB uB vB aB (&0) (&543 / &500) /\
    linside cB sB uB vB aB (&2 / &5) (&1) /\
    (forall x y. linside cB sB uB vB aB x y ==> y <= &2) /\
    ~linside cB sB uB vB aB (--(&13) / &50) (&1) /\
    linside cK sK uK vK aK (&543 / &500) (&1) /\
    linside cK sK uK vK aK (&1) (&1) /\
    (forall x y. linside cK sK uK vK aK x y ==> x <= &2 /\ y <= &2)`;;

(* the chart translate (pullX W) 2 (-2) *)
let C1089CC_CHART = prove
 (`forall c s u v a x y.
     linside (--c) s (u - &2 * c + &2 * s) (--v - a - &2 * s - &2 * c) a x y <=>
     linside c s u v a (&2 - x) (y - &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1089CC_CHART_CENTER = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcy (--c) s (u - &2 * c + &2 * s) (--v - a - &2 * s - &2 * c) a =
         lcy c s u v a + &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcy] THEN CONV_TAC REAL_RING);;

(* Lean: right_near *)
let C1089CC_RIGHT_NEAR = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aW /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> linside cW sW uW vW aW (&1) (&39 / &100)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--cW:real`; `sW:real`; `uW - &2 * cW + &2 * sW`;
                `--vW - aW - &2 * sW - &2 * cW`; `aW:real`; `&239 / &100`] WSC_CHORD) THEN
  ASM_SIMP_TAC[C1089CC_CHART; C1089CC_CHART_CENTER] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG];
    REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o
      check (fun t -> is_forall(concl t) && not(is_neg(snd(strip_forall(concl t))))))) THEN
    REAL_ARITH_TAC;
    ASM_MESON_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* Lean: right_bar *)
let C1089CC_RIGHT_BAR = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cB sB uB vB aB cK sK uK vK aK.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     c1089cc_input cC sC uC vC aC cW sW uW vW aW cB sB uB vB aB cK sK uK vK aK
     ==> linside cB sB uB vB aB (&14 / &25) (&1) /\
         forall y. &0 <= y ==> y <= &39 / &100 ==> linside cW sW uW vW aW (&1) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1089cc_input] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`]
    OC1089CO_RIGHT_ORIGIN_OF_POINTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN REWRITE_TAC[ldisj] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[]) THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C1089CC_RIGHT_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OCWPVG_VERTICAL_OWNED THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ldisj (unfolded) of the frame square c1 s1 u1 v1 against the square with
   cosine variable cX, at the point (p, q) *)
let C1089CC_APART_TAC cX p q =
  FIRST_ASSUM(MP_TAC o SPECL [p; q] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `c1:real`)) (concl th) &&
    can (find_term ((=) cX)) (concl th))) THEN
  (fun (asl,w as g) ->
     REWRITE_TAC(filter (fun th -> not(is_forall(concl th))) (map snd asl)) g);;

(* a point W 1 y of the right bar *)
let C1089CC_BAR_TAC y =
  SUBGOAL_THEN (subst [y,`y:real`] `linside cW sW uW vW aC (&1) y`) ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&39 / &100`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC];;

(* Lean: points *)
let C1089CC_POINTS = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cB sB uB vB aB cK sK uK vK aK.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     c1089cc_input cC sC uC vC aC cW sW uW vW aW cB sB uB vB aB cK sK uK vK aK
     ==> linside cC sC uC vC aC (&0) (&0) /\ linside cW sW uW vW aW (&1) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`]
    C1089CC_RIGHT_BAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c1089cc_input] o
    check (fun th -> fst(strip_comb(concl th)) = `c1089cc_input`)) THEN
  REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `aC:real`))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = aC`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && is_iff(snd(strip_forall(concl th))) then
      (RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th])
    else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC C1092IBC_POINT THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      C1089CC_APART_TAC `cB:real` `&2 / &5` `&1`;
      C1089CC_APART_TAC `cB:real` `&14 / &25` `&1`;
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN C1089CC_BAR_TAC `y:real` THEN
      C1089CC_APART_TAC `cW:real` `&1` `y:real`];
    ALL_TAC] THEN
  ASM_CASES_TAC `linside c1 s1 u1 v1 aC (&1) (&2 / &5)` THENL
   [MATCH_MP_TAC C1089CAC_POINT THEN
    MAP_EVERY EXISTS_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] THEN
    ASM_REWRITE_TAC[ldisj] THEN C1089CC_APART_TAC `cB:real` `&2 / &5` `&1`;
    ALL_TAC] THEN
  ASM_CASES_TAC `linside c1 s1 u1 v1 aC (&0) (&0)` THEN ASM_REWRITE_TAC[] THEN
  C1089CC_BAR_TAC `&39 / &100` THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
    OCCN_IMPOSSIBLE) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[ldisj] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1089CC_APART_TAC `cB:real` `&2 / &5` `&1`);;
