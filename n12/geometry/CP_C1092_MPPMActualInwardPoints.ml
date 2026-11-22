(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardPoints.lean              *)
(* (N12Compact.C1092MPPMActualInward).  Original-owner producers for the     *)
(* inward pipeline.  (Lean header: "Source only, uncompiled".)               *)
(* Conventions of CP_C1092_MPPMOmissionCenter.ml / MPPMOmissions.ml (owners  *)
(* p i at mask EL i c1092wc_code, side l; WallContext p mppm C1092MPPE_CTX;  *)
(* Inward = c1092mcc_inward; g.pullPacking p is (d1,d2,e1,e2) with           *)
(* c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2), family/owners/context transport *)
(* C1092OT_FAMILY_TRANSPORT / C1092OT_OWNERS_TRANSPORT /                     *)
(* C1092CT_CONTEXT_TRANSPORT, pulled insides C1092CT_INSIDE_PULL).           *)
(* Frame p i C is c1092mpai_frame c1 c2 a b l i cC sC uC vC aC; chart p i is *)
(* the tuple c1092mpai_chart i ((owners p i).translated 2 2, inside through  *)
(* C1092PSA_INSIDE_TRANSLATED).  marker_owned is C1092MOC_MARKER_POINT       *)
(* (markers via oo_seed), side_gt OO_SIDE, side_same l = l.  Used:           *)
(* MPPMInwardNeighbors.southeast_pair / northwest_pair C1092MIN_*;           *)
(* MPPMPositiveSeedsActual.missing_halfpoint / bottom_origin_of_halfpoint    *)
(* C1092PSA_*; MPPMActualWallReduction no_missing / wall_pairs (via          *)
(* C1092MPAWR_*_ORDINARY); WallProfile.vertical_owned OCWPVG_VERTICAL_OWNED; *)
(* inside_segment (horizontal form C1092MPAI_HORIZONTAL_OWNED);              *)
(* BottomCorner c1092ifc_bottomCorner; PredecessorPoints                     *)
(* c1092ifcc_predecessorPoints; InwardPoint.strong_original                  *)
(* CCIP_STRONG_ORIGINAL; ClosedFrames.canonical_frame CLF_CANONICAL_FRAME.   *)
(* Tag C1092MPAI_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualWallReduction.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardNeighbors.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveSeedsActual.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCenteredCaps.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCentered.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

(* Lean: side_gt *)
let C1092MPAI_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`, REWRITE_TAC[OO_SIDE]);;
(* Lean: side_same *)
let C1092MPAI_SIDE_SAME = prove (`forall l:real. l = l`, REWRITE_TAC[]);;
(* Lean: marker_owned *)
let C1092MPAI_MARKER_OWNED = C1092MOC_MARKER_POINT;;

(* Lean: Frame (structure; fields side, actual) *)
let c1092mpai_frame = new_definition
 `c1092mpai_frame (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (i:num)
                  (cC:real) (sC:real) (uC:real) (vC:real) (aC:real) <=>
    aC = l /\
    forall x y. linside cC sC uC vC aC x y <=>
          linside (ooc c1 c2 a b l (EL i c1092wc_code)) (oos c1 c2 a b l (EL i c1092wc_code))
                  (oou c1 c2 a b l (EL i c1092wc_code)) (oov c1 c2 a b l (EL i c1092wc_code)) l
                  (&2 + x) (&2 + y)`;;

(* Lean: chart  ((owners p i).translated 2 2 as a 5-tuple; i a numeral string or "i") *)
let c1092mpai_chart i =
  let ow f = Printf.sprintf "(%s c1 c2 a b l (EL %s c1092wc_code))" f i in
  map parse_term
    [ow "ooc"; ow "oos";
     Printf.sprintf "%s - (%s * &2 + %s * &2)" (ow "oou") (ow "ooc") (ow "oos");
     Printf.sprintf "%s - (--%s * &2 + %s * &2)" (ow "oov") (ow "oos") (ow "ooc");
     "l:real"];;
let c1092mpai_chin i x y = list_mk_comb(`linside`, c1092mpai_chart i @ [x; y]);;

(* Lean: chart_frame *)
let C1092MPAI_CHART_FRAME = prove
 (list_mk_forall(C1092MPPE_V @ [`i:num`],
    list_mk_comb(`c1092mpai_frame`, C1092MPPE_V @ [`i:num`] @ c1092mpai_chart "i")),
  REWRITE_TAC[c1092mpai_frame; C1092PSA_INSIDE_TRANSLATED]);;

(* Lean: canonical_frame *)
let C1092MPAI_CANONICAL_FRAME = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l
     ==> exists cC sC uC vC aC. cC * cC + sC * sC = &1 /\ &0 < aC /\
           c1092mpai_frame c1 c2 a b l i cC sC uC vC aC /\ &0 < cC /\ abs sC <= cC`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL (c1092mpai_chart "i") CLF_CANONICAL_FRAME) THEN
  ASM_SIMP_TAC[OO_UNIT; OO_SIDE; REAL_ARITH `&1 < l ==> &0 < l`] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  REWRITE_TAC[c1092mpai_frame; C1092PSA_INSIDE_TRANSLATED] THEN MESON_TAC[]);;

(* Lean: Frame.apart *)
let C1092MPAI_FRAME_APART = prove
 (`forall c1 c2 a b l i j cC sC uC vC aC cD sD uD vD aD.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092mpai_frame c1 c2 a b l i cC sC uC vC aC /\
     c1092mpai_frame c1 c2 a b l j cD sD uD vD aD /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj cC sC uC vC aC cD sD uD vD aD`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mpai_frame] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`i:num`; `j:num`]) C1092WC_OWNERS_DISJOINT) THEN
  ASM_REWRITE_TAC[ldisj] THEN MESON_TAC[]);;

(* the horizontal form of WallProfile.vertical_owned / inside_segment *)
let C1092MPAI_HORIZONTAL_OWNED = prove
 (`forall c s u v a y b h.
      b < h /\ linside c s u v a b y /\ linside c s u v a h y
      ==> forall x. b <= x ==> x <= h ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `c:real`; `u:real`; `--v - a:real`; `a:real`; `y:real`; `b:real`; `h:real`]
    OCWPVG_VERTICAL_OWNED) THEN
  ASM_REWRITE_TAC[LINSIDE_PULLSW]);;

(* apply th (stated for a packing d1 d2 e1 e2 l with WallContext mppm) to g.pullPacking p;
   owners idx of the pulled packing are rewritten to original owners; the original
   point facts must be in the assumptions *)
let c1092mpai_transport g th idx =
  let v4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
  let d5 = [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`] in
  SUBGOAL_THEN (mk_exists(`d1:num->real`, list_mk_exists([`d2:num->real`; `e1:num->real`; `e2:num->real`],
     mk_eq(list_mk_comb(`c1092ot_pk`, [g; `(c1:num->real,c2:num->real,a:num->real,b:num->real)`]),
           `(d1:num->real,d2:num->real,e1:num->real,e2:num->real)`))))
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `NPACK d1 d2 e1 e2 l` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1092wc_ctx d1 d2 e1 e2 l c1092mppe_mppm` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092MMEN_CTX_CONG THEN
    EXISTS_TAC (mk_comb(mk_comb(`c1092ws_branch_action`, g), `c1092mppe_mppm`)) THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN CONV_TAC c1092ae_act_conv THEN
      REWRITE_TAC[c1092mppe_mppm] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN MAP_EVERY EXISTS_TAC v4 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL d5 th) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL ([g] @ v4 @ [`l:real`] @ fst (chop_list 4 d5) @ [mk_small_numeral i]) C1092OT_OWNERS_TRANSPORT) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th])) idx THEN
  REWRITE_TAC(map (fun i -> c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), mk_small_numeral i))) idx) THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

let C1092MPAI_HYPS = Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s" C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4;;
let c1092mpai_use th = MP_TAC(SPECL C1092MPPE_V th) THEN ASM_REWRITE_TAC[];;
let C1092MPAI_NO_MISSING_TAC =
  c1092mpai_use C1092MPAWR_NO_MISSING THEN DISCH_TAC;;
let C1092MPAI_INWARD_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcc_inward] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c1092mcc_inward`));;

(* Lean: successor_halfpoint *)
let C1092MPAI_SUCCESSOR_HALFPOINT = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MPAI_HYPS (c1092mppe_in 5 "&5 / &2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092MIN_SOUTHEAST_PAIR THEN STRIP_TAC THEN C1092MPAI_INWARD_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mppe_in 5 "&2" "&87 / &50"))) ASSUME_TAC THENL
   [MP_TAC(SPECL (C1092MPPE_V @ [`5`; `4`]) C1092WC_OWNERS_DISJOINT) THEN
    ASM_REWRITE_TAC[ldisj; ARITH] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&87 / &50`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  c1092mpai_transport `(true,true,false)` C1092PSA_MISSING_HALFPOINT [4]);;

(* Lean: right_origin *)
let C1092MPAI_RIGHT_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MPAI_HYPS (c1092mppe_in 10 "&3" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAI_SUCCESSOR_HALFPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAWR_RIGHT_ORDINARY THEN DISCH_TAC THEN
  c1092mpai_transport `(true,true,false)` C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT [4; 9]);;

(* Lean: right_bar *)
let C1092MPAI_RIGHT_BAR = prove
 (parse_term (Printf.sprintf "!%s. %s ==> !y. --(&2 / &5) <= y ==> y <= &0 ==> %s"
    C1092AE_P C1092MPAI_HYPS (string_of_term (c1092mpai_chin "10" `&1` `y:real`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAI_RIGHT_ORIGIN THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAWR_RIGHT_ORDINARY THEN DISCH_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MP_TAC(ISPECL (map parse_term
    ["ooc c1 c2 a b l (EL 10 c1092wc_code)"; "oos c1 c2 a b l (EL 10 c1092wc_code)";
     "oou c1 c2 a b l (EL 10 c1092wc_code)"; "oov c1 c2 a b l (EL 10 c1092wc_code)"; "l:real";
     "&3"; "&8 / &5"; "&2"]) OCWPVG_VERTICAL_OWNED) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  MAP_EVERY UNDISCH_TAC [`--(&2 / &5) <= y`; `y <= &0`] THEN REAL_ARITH_TAC);;

(* Lean: bottom_bar *)
let C1092MPAI_BOTTOM_BAR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> !x. --(&2 / &5) <= x ==> x <= --(&13 / &50) ==> %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX (string_of_term (c1092mpai_chin "9" `x:real` `--(&1)`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MP_TAC(ISPECL (map parse_term
    ["ooc c1 c2 a b l (EL 9 c1092wc_code)"; "oos c1 c2 a b l (EL 9 c1092wc_code)";
     "oou c1 c2 a b l (EL 9 c1092wc_code)"; "oov c1 c2 a b l (EL 9 c1092wc_code)"; "l:real";
     "&1"; "&8 / &5"; "&87 / &50"]) C1092MPAI_HORIZONTAL_OWNED) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  MAP_EVERY UNDISCH_TAC [`--(&2 / &5) <= x`; `x <= --(&13 / &50)`] THEN REAL_ARITH_TAC);;

(* Lean: bottom_corner *)
let C1092MPAI_BOTTOM_CORNER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MPPE_CTX
    (string_of_term (list_mk_comb(`c1092ifc_bottomCorner`, c1092mpai_chart "9" @ c1092mpai_chart "0")))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  REWRITE_TAC[c1092ifc_bottomCorner; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
  CONV_TAC C1092MOC_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  let box i = REWRITE_RULE[lcont] (c1092moc_box i) in
  ASM_REWRITE_TAC[c1092moc_side (); c1092moc_seed 9 (`&2`, `&457 / &500`);
    c1092moc_seed 0 (`&1`, `&457 / &500`); c1092moc_seed 0 (`&1`, `&1`); c1092moc_apart 0 9] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (DISCH_THEN(MP_TAC o MATCH_MP (box 9)) ORELSE DISCH_THEN(MP_TAC o MATCH_MP (box 0))) THEN
  REAL_ARITH_TAC);;

(* Lean: predecessor_points *)
let C1092MPAI_PREDECESSOR_POINTS = prove
 (parse_term (Printf.sprintf "!%s cW sW uW vW aW. %s /\\ cW * cW + sW * sW = &1 /\\ &0 < aW /\\
      c1092mpai_frame %s 7 cW sW uW vW aW ==> c1092ifcc_predecessorPoints cW sW uW vW aW"
    C1092AE_P C1092MPAI_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092MIN_NORTHWEST_PAIR THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpai_frame] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c1092mpai_frame`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = l`)) THEN
  REWRITE_TAC[c1092ifcc_predecessorPoints] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092MOC_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN
  ASM_REWRITE_TAC[c1092moc_seed 7 (`&33 / &20`, `&47 / &20`);
    c1092moc_excl 7 11 (c1092moc_seed 11 (`&2`, `&1543 / &500`));
    c1092moc_excl 7 3 (c1092moc_seed 3 (`&1`, `&3`));
    c1092moc_excl 7 3 (c1092moc_seed 3 (`&1`, `&1543 / &500`))]);;

(* Lean: missing_outer_sharp *)
let C1092MPAI_MISSING_OUTER_SHARP = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ c1092mcc_inward %s /\\ ~%s ==> %s"
    C1092AE_P C1092AE_HYP C1092MCC_OWN4 (c1092mppe_in 4 "&1" "&8 / &5") (c1092mppe_in 4 "&199 / &100" "&73 / &50")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAI_INWARD_TAC THEN
  CONV_TAC C1092MOC_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN
  let t, eqs = c1092moc_layers 4 [C1092MOC_Y; C1092MOC_SW] in
  let a4 x y = ASSUME (list_mk_comb(`linside`, c1092moc_own 4 @ [x; y])) in
  ACCEPT_TAC (c1092moc_apply (c1092moc_conv eqs) (SPECL t CCIP_STRONG_ORIGINAL)
    [c1092moc_punit 4 t; c1092moc_side ();
     c1092moc_seed 4 (`&33 / &20`, `&33 / &20`); a4 `&87 / &50` `&2`; a4 `&2` `&87 / &50`;
     c1092moc_excl 4 7 (c1092moc_seed 7 (`&33 / &20`, `&47 / &20`));
     c1092moc_excl 4 5 (c1092moc_seed 5 (`&47 / &20`, `&33 / &20`));
     ASSUME (mk_neg (list_mk_comb(`linside`, c1092moc_own 4 @ [`&1`; `&8 / &5`])))]));;
