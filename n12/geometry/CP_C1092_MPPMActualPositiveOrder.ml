(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualPositiveOrder.lean             *)
(* (N12Compact.C1092MPPMActualPositiveOrder).  The actual positive OOOO      *)
(* sector before the wall-order cancellation.  (Lean header: "Source only,   *)
(* uncompiled".)  Conventions of CP_C1092_MPPMOmissions.ml /                 *)
(* CP_C1092_MPPMPositiveSeedsActual.ml: owners p i at mask EL i              *)
(* c1092wc_code, side l; WallContext p mppm C1092MPPE_CTX; ActualFrame p C   *)
(* is c1092psa_frame (C's OpenSquare invariants as explicit hypotheses);     *)
(* Normal = c977cc_normal; half = C1092WPS_half; cosH / sinH c1092sps_*.     *)
(* (rotation i).pullPacking p is (d1,d2,e1,e2) with                          *)
(* c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2), i < 4; *)
(* family / owners / context transport C1092OT_FAMILY_TRANSPORT /            *)
(* C1092OT_OWNERS_TRANSPORT / C1092CT_CONTEXT_TRANSPORT (+ C1092OT_NPACK).   *)
(* (owners p i).translated 2 2 is the tuple of c1092mpai_chart               *)
(* (C1092PSA_INSIDE_TRANSLATED); center_translate_x/y by REAL_ARITH with the *)
(* unit normal.  Used: MPPMOrdinaryWallAdvance all_far_no_omission /         *)
(* bottom_bar_no_omission C1092OWA_*; MPPMPositiveSeedsActual missing_inputs *)
(* / forward_core / forward_halfpoint_and_origin / bottom_origin_of_missing  *)
(* C1092PSA_*; MPPMMissingPositiveBoundaries Data / of_inputs / order        *)
(* c1092mpbp_data / C1092MPBP_DATA_OF_INPUTS / C1092MPBE_ORDER;              *)
(* C1092ShallowWallOrder Data / order c1092sbo_data / C1092SLO_ORDER;        *)
(* PositiveCrosspointSeeds.forward_profile C1092PCS_FORWARD_PROFILE;         *)
(* quarter_data C1092WPS_QUARTER_DATA; short_projections                     *)
(* WFP_SHORT_PROJECTIONS; MPPMActualWallReduction C1092MPAWR_*.              *)
(* The private side_gt / side_same / mark are OO_SIDE / l = l / oo_seed.     *)
(* The centerPairs bookkeeping of rotated_orders_impossible is replaced by   *)
(* direct center algebra of the pulled owners.  Tag C1092MPAPO_.             *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualWallReduction.ml";;
needs "n12/geometry/CP_C1092_MPPMActualInwardPoints.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveSector.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundEnvelopes.ml";;
needs "n12/geometry/CP_C1092_MPPMWallOrderCycle.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryWallAdvance.ml";;
needs "n12/geometry/CP_C1092_ShallowLeftOrder.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveCrosspointSeeds.ml";;
needs "n12/geometry/C1092ShallowPositiveScalars.ml";;

let C1092MPAPO_V4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`];;
let C1092MPAPO_CV = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let c1092mpapo_d4 k = map (fun n -> mk_var(n ^ k, `:num->real`)) ["d1"; "d2"; "e1"; "e2"];;
let c1092mpapo_in = c1092mppe_in;;
let c1092mpapo_dpk = "c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2)";;
let c1092mpapo_din i x y = c1092ae_in "d1 d2 e1 e2 l" i x y;;

(* Lean: Ordinary (structure) *)
let c1092mpapo_ordinary = new_definition (parse_term (Printf.sprintf
  "c1092mpapo_ordinary (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
     (%s /\\ %s) /\\ (%s /\\ %s) /\\ (%s /\\ %s) /\\ (%s /\\ %s)"
  (c1092mpapo_in 4 "&1" "&87 / &50") (c1092mpapo_in 4 "&1" "&8 / &5")
  (c1092mpapo_in 5 "&12 / &5" "&1") (c1092mpapo_in 5 "&113 / &50" "&1")
  (c1092mpapo_in 6 "&3" "&113 / &50") (c1092mpapo_in 6 "&3" "&12 / &5")
  (c1092mpapo_in 7 "&8 / &5" "&3") (c1092mpapo_in 7 "&87 / &50" "&3")));;

(* Lean: rotation *)
let c1092mpapo_rotation = new_definition
 `c1092mpapo_rotation = [(false,false,false); (true,true,false); (false,true,true); (true,false,true)]`;;
let C1092MPAPO_ROT_ELS = Array.to_list (el_lookups c1092mpapo_rotation);;
let C1092MPAPO_ROTS = [`(false,false,false)`; `(true,true,false)`; `(false,true,true)`; `(true,false,true)`];;

let C1092MPAPO_HYPS = Printf.sprintf "%s /\\ %s /\\ c1092mpapo_ordinary %s" C1092AE_HYP C1092MPPE_CTX C1092AE_P;;
let c1092mpapo_use th = MP_TAC(SPECL C1092MPPE_V th) THEN ASM_REWRITE_TAC[];;
let c1092mpapo_head c th = is_comb (concl th) && fst (strip_comb (concl th)) = c;;
let C1092MPAPO_ORD_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpapo_ordinary] o
    check (fun th -> c1092mpapo_head `c1092mpapo_ordinary` th &&
                     hd (snd (strip_comb (concl th))) = `c1:num->real`));;
let C1092MPAPO_NO_MISSING_TAC = c1092mpapo_use C1092MPAWR_NO_MISSING THEN DISCH_TAC;;

(* ~ owner i at (x,y), from owner j at (x,y) in the assumptions (EL form) *)
let c1092mpapo_excl_tac i j x y =
  MP_TAC(SPECL (C1092MPPE_V @ [mk_small_numeral i; mk_small_numeral j]) C1092WC_OWNERS_DISJOINT) THEN
  ASM_REWRITE_TAC[ldisj; ARITH] THEN DISCH_THEN(MP_TAC o SPECL [x; y]) THEN ASM_REWRITE_TAC[];;

(* rewrite the frame equivalence of C into the goal *)
let C1092MPAPO_FRAME_TAC =
  FIRST_ASSUM(fun th -> if c1092mpapo_head `c1092psa_frame` th
    then REWRITE_TAC[CONJUNCT2 (REWRITE_RULE[c1092psa_frame] th)] else NO_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV);;

(* rewrite owners idx of the packing d (pk g p = d in the assumptions) to original owners *)
let c1092mpapo_pull_tac d4 g idx =
  MAP_EVERY (fun i ->
    MP_TAC(SPECL ([g] @ C1092MPAPO_V4 @ [`l:real`] @ d4 @ [mk_small_numeral i]) C1092OT_OWNERS_TRANSPORT) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th])) idx THEN
  REWRITE_TAC(map (fun i -> c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), mk_small_numeral i))) idx) THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];;
(* the same with g read off the pk assumption *)
let c1092mpapo_gpull_tac idx =
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && is_comb (lhs c) && fst (strip_comb (lhs c)) = `c1092ot_pk`
    then c1092mpapo_pull_tac (c1092mpapo_d4 "") (rand (rator (lhs c))) idx else NO_TAC);;
let C1092MPAPO_ENUM_TAC =
  C1092WP_ENUM_TAC `i:num` 4 THEN RULE_ASSUM_TAC(REWRITE_RULE C1092MPAPO_ROT_ELS) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS;;

(* Lean: rotation_context *)
let C1092MPAPO_ROTATION_CONTEXT = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2 i. %s /\\ %s /\\ i < 4 /\\ %s ==> c1092wc_ctx d1 d2 e1 e2 l c1092mppe_mppm"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX c1092mpapo_dpk),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ENUM_TAC THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && is_comb (lhs c) && fst (strip_comb (lhs c)) = `c1092ot_pk` then
      let g = rand (rator (lhs c)) in
      MATCH_MP_TAC C1092MMEN_CTX_CONG THEN
      EXISTS_TAC (mk_comb(mk_comb(`c1092ws_branch_action`, g), `c1092mppe_mppm`)) THEN CONJ_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN CONV_TAC c1092ae_act_conv THEN
        REWRITE_TAC[c1092mppe_mppm] THEN CONV_TAC NUM_REDUCE_CONV;
        MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN MAP_EVERY EXISTS_TAC C1092MPAPO_V4 THEN
        ASM_REWRITE_TAC[]]
    else NO_TAC));;

(* Lean: Ordinary.rotated *)
let C1092MPAPO_ORDINARY_ROTATED = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2 i. %s /\\ c1092mpapo_ordinary %s /\\ i < 4 /\\ %s
      ==> c1092mpapo_ordinary d1 d2 e1 e2 l" C1092AE_P C1092AE_HYP C1092AE_P c1092mpapo_dpk),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN C1092MPAPO_ENUM_TAC THEN
  REWRITE_TAC[c1092mpapo_ordinary] THEN c1092mpapo_gpull_tac [4; 5; 6; 7] THEN ASM_REWRITE_TAC[]);;

(* Lean: side_gt (private) *)
let C1092MPAPO_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`, REWRITE_TAC[OO_SIDE]);;
(* Lean: side_same (private) *)
let C1092MPAPO_SIDE_SAME = prove (`forall l:real. l = l`, REWRITE_TAC[]);;
(* Lean: mark (private) *)
let C1092MPAPO_MARK = C1092MOC_MARKER_POINT;;

(* Lean: far_points *)
let C1092MPAPO_FAR_POINTS = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s /\\ %s /\\ %s /\\ %s" C1092AE_P C1092MPAPO_HYPS
    (c1092mpapo_in 8 "&1" "&64 / &25") (c1092mpapo_in 9 "&36 / &25" "&1")
    (c1092mpapo_in 10 "&3" "&36 / &25") (c1092mpapo_in 11 "&64 / &25" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN C1092MPAPO_NO_MISSING_TAC THEN
  MATCH_MP_TAC (SPECL C1092MPPE_V C1092OWA_ALL_FAR_NO_OMISSION) THEN ASM_REWRITE_TAC[]);;

(* Lean: bottom_bar *)
let C1092MPAPO_BOTTOM_BAR = prove
 (parse_term (Printf.sprintf "!%s x. %s /\\ &36 / &25 <= x /\\ x <= &87 / &50 ==> %s" C1092AE_P C1092MPAPO_HYPS
    (c1092mpapo_in 9 "x" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN C1092MPAPO_NO_MISSING_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MPPE_V @ [`x:real`]) C1092OWA_BOTTOM_BAR_NO_OMISSION) THEN ASM_REWRITE_TAC[]);;

let C1092MPAPO_CHYPS = "cC * cC + sC * sC = &1 /\\ &0 < aC /\\ c1092psa_frame c1 c2 a b l cC sC uC vC aC /\\ c977cc_normal cC sC";;

(* Lean: missing_data *)
let C1092MPAPO_MISSING_DATA = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\ %s /\\ %s ==> c1092mpbp_data cC sC uC vC aC"
    C1092AE_P C1092MPAPO_HYPS (c1092mpapo_in 4 "&87 / &50" "&2") (c1092mpapo_in 8 "&1" "&2") C1092MPAPO_CHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092MPBP_DATA_OF_INPUTS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAPO_CV) C1092PSA_MISSING_INPUTS) THEN ASM_REWRITE_TAC[];
    C1092MPAPO_FRAME_TAC THEN c1092mpapo_excl_tac 4 8 `&1` `&2`]);;

(* Lean: retaining_lower_v *)
let C1092MPAPO_RETAINING_LOWER_V = prove
 (`forall cC sC uC vC aC.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ &1 < aC /\ c977cc_normal cC sC /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     uC + aC <= --sC / &2 /\
     ~linside cC sC uC vC aC (--(&14 / &25)) (--(&1))
     ==> (&14 / &25) * sC - cC <= vC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `&14 / &25`; `&1 / &2`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside cC sC uC vC aC (--(&14 / &25)) (--(&1))` THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

let C1092MPAPO_RHYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ %s /\\ &0 < sC"
  C1092MPAPO_HYPS (c1092mpapo_in 4 "&87 / &50" "&2") (c1092mpapo_in 8 "&1" "&2")
  (c1092mpapo_in 5 "&2" "&3 / &2") C1092MPAPO_CHYPS;;

(* Lean: retaining_data *)
let C1092MPAPO_RETAINING_DATA = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ C1092WPS_half cC sC <= &1 / &4
      ==> c1092sbo_data cC sC uC vC aC (C1092WPS_half cC sC)" C1092AE_P C1092MPAPO_RHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092mpapo_head `c1092psa_frame`)) THEN
    MP_TAC(SPECL C1092MPPE_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mpapo_in 4 "&1" "&2"))) ASSUME_TAC THENL
   [c1092mpapo_excl_tac 4 8 `&1` `&2`; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAPO_CV) C1092PSA_FORWARD_CORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MPAPO_CV C1092PCS_FORWARD_PROFILE) THEN
  ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN STRIP_TAC THEN
  SUBGOAL_THEN `C1092WPS_half cC sC <= &1 / &3` ASSUME_TAC THENL
   [UNDISCH_TAC `C1092WPS_half cC sC <= &1 / &4` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAPO_CV) C1092PSA_FORWARD_HALFPOINT_AND_ORIGIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092pcs_forwardCore] o
    check (c1092mpapo_head `c1092pcs_forwardCore`)) THEN
  SUBGOAL_THEN `~linside cC sC uC vC aC (--(&14 / &25)) (--(&1))` ASSUME_TAC THENL
   [C1092MPAPO_FRAME_TAC THEN c1092mpapo_excl_tac 4 9 `&36 / &25` `&1`; ALL_TAC] THEN
  MP_TAC(SPECL C1092MPAPO_CV C1092MPAPO_RETAINING_LOWER_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  SUBGOAL_THEN `&0 < C1092WPS_half cC sC` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []); STRIP_TAC] THEN
  SUBGOAL_THEN `cC = c1092sps_cosH (C1092WPS_half cC sC)` ASSUME_TAC THENL
   [REWRITE_TAC[c1092sps_cosH] THEN SIMP_TAC[REAL_EQ_RDIV_EQ; C1092SPS_HALF_DEN_POS] THEN
    UNDISCH_TAC `(&1 + C1092WPS_half cC sC pow 2) * cC = &1 - C1092WPS_half cC sC pow 2` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sC = c1092sps_sinH (C1092WPS_half cC sC)` ASSUME_TAC THENL
   [REWRITE_TAC[c1092sps_sinH] THEN SIMP_TAC[REAL_EQ_RDIV_EQ; C1092SPS_HALF_DEN_POS] THEN
    UNDISCH_TAC `(&1 + C1092WPS_half cC sC pow 2) * sC = &2 * C1092WPS_half cC sC` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092sbo_data] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* the literal-mask chart (owners p i).translated 2 2 *)
let c1092mpapo_chart i =
  map (fun t -> rhs (concl (REWRITE_CONV (Array.to_list C1092WC_CODE_EL) t)))
    (c1092mpai_chart (string_of_int i));;

(* antecedents of the shared order theorems, in literal-mask form *)
let c1092mpapo_ants_tac () =
  let fr = CONJUNCTS (REWRITE_RULE[c1092psa_frame] (ASSUME (parse_term C1092PSA_FRAME))) in
  let acl = hd fr and feq = CONV_RULE C1092MOC_CODE_CONV (el 1 fr) in
  let pts = [c1092moc_seed 9 (`&2`, `&457 / &500`); c1092moc_seed 8 (`&457 / &500`, `&2`);
             c1092moc_unit 9; c1092moc_unit 8; c1092moc_pos ()] in
  let aps = [c1092moc_apart 4 9; c1092moc_apart 4 8] in
  let boxes = [REWRITE_RULE[lcont] (c1092moc_box 9); REWRITE_RULE[lcont] (c1092moc_box 8)] in
  REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED; feq] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; MAP_FIRST ACCEPT_TAC pts;
         REWRITE_TAC aps THEN NO_TAC;
         REPEAT GEN_TAC THEN FIRST (map (fun b -> DISCH_THEN(MP_TAC o MATCH_MP b)) boxes) THEN
           REAL_ARITH_TAC;
         MP_TAC (end_itlist CONJ [acl; c1092moc_side (); c1092moc_cap ()]) THEN REAL_ARITH_TAC];;
let C1092MPAPO_CENTER_TAC =
  MP_TAC (c1092moc_unit 9) THEN MP_TAC (c1092moc_unit 8) THEN
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC;;
let C1092MPAPO_ORDER_CONCL = Printf.sprintf "&4 < lcx %s + lcy %s"
  (c1092ae_own C1092AE_P 9) (c1092ae_own C1092AE_P 8);;

(* Lean: retaining_order *)
let C1092MPAPO_RETAINING_ORDER = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ C1092WPS_half cC sC <= &1 / &4 ==> %s"
    C1092AE_P C1092MPAPO_RHYPS C1092MPAPO_ORDER_CONCL),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAPO_CV) C1092MPAPO_RETAINING_DATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  CONV_TAC C1092MOC_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN
  MP_TAC(SPECL (C1092MPAPO_CV @ c1092mpapo_chart 9 @ c1092mpapo_chart 8 @ [`C1092WPS_half cC sC`])
    C1092SLO_ORDER) THEN
  ANTS_TAC THENL [c1092mpapo_ants_tac (); C1092MPAPO_CENTER_TAC]);;

(* Lean: missing_order *)
let C1092MPAPO_MISSING_ORDER = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\ %s /\\ %s ==> %s"
    C1092AE_P C1092MPAPO_HYPS (c1092mpapo_in 4 "&87 / &50" "&2") (c1092mpapo_in 8 "&1" "&2")
    C1092MPAPO_CHYPS C1092MPAPO_ORDER_CONCL),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAPO_CV) C1092MPAPO_MISSING_DATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  CONV_TAC C1092MOC_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN
  MP_TAC(SPECL (C1092MPAPO_CV @ c1092mpapo_chart 9 @ c1092mpapo_chart 8) C1092MPBE_ORDER) THEN
  ANTS_TAC THENL [c1092mpapo_ants_tac (); C1092MPAPO_CENTER_TAC]);;

let C1092MPAPO_SHYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ &0 < sC /\\ (%s ==> C1092WPS_half cC sC <= &1 / &4)"
  C1092MPAPO_HYPS (c1092mpapo_in 8 "&1" "&2") (c1092mpapo_in 5 "&2" "&3 / &2") C1092MPAPO_CHYPS
  (c1092mpapo_in 4 "&87 / &50" "&2");;

(* Lean: sector_order *)
let C1092MPAPO_SECTOR_ORDER = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> %s" C1092AE_P C1092MPAPO_SHYPS C1092MPAPO_ORDER_CONCL),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term (c1092mpapo_in 4 "&87 / &50" "&2")) THENL
   [MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAPO_CV) C1092MPAPO_RETAINING_ORDER) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAPO_CV) C1092MPAPO_MISSING_ORDER) THEN
    ASM_REWRITE_TAC[]]);;

(* Lean: MissingForward (structure) *)
let c1092mpapo_missingForward = new_definition (parse_term (Printf.sprintf
  "c1092mpapo_missingForward (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
     ~%s /\\ ~%s /\\ ~%s /\\ ~%s"
  (c1092mpapo_in 4 "&87 / &50" "&2") (c1092mpapo_in 5 "&2" "&87 / &50")
  (c1092mpapo_in 6 "&113 / &50" "&2") (c1092mpapo_in 7 "&2" "&113 / &50")));;

(* Lean: missing_forward_rotated *)
let C1092MPAPO_MISSING_FORWARD_ROTATED = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2 i. %s /\\ c1092mpapo_missingForward %s /\\ i < 4 /\\ %s ==> ~%s"
    C1092AE_P C1092AE_HYP C1092AE_P c1092mpapo_dpk (c1092mpapo_din 4 "&87 / &50" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpapo_missingForward] o
    check (c1092mpapo_head `c1092mpapo_missingForward`)) THEN
  C1092MPAPO_ENUM_TAC THEN c1092mpapo_gpull_tac [4] THEN ASM_REWRITE_TAC[]);;

(* the pulled packing d of rotation i, with its NPACK / IMAGE / context facts *)
let c1092mpapo_rot_tac k i =
  let g = el i C1092MPAPO_ROTS and d4 = c1092mpapo_d4 k in
  SUBGOAL_THEN (list_mk_exists(d4,
     mk_eq(list_mk_comb(`c1092ot_pk`, [g; `(c1:num->real,c2:num->real,a:num->real,b:num->real)`]),
           mk_pair(el 0 d4, mk_pair(el 1 d4, mk_pair(el 2 d4, el 3 d4))))))
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN (list_mk_comb(`NPACK`, d4 @ [`l:real`])) ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: C1092MPAPO_V4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`IMAGE binarysum`, list_mk_comb(`FFP`, d4 @ [`l:real`])), `c1092wc_family`))
    ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: C1092MPAPO_V4) THEN
    ASM_REWRITE_TAC[]; ALL_TAC];;
let c1092mpapo_rot_use th k i =
  MP_TAC(SPECL (C1092MPPE_V @ c1092mpapo_d4 k @ [mk_small_numeral i]) th) THEN
  ASM_REWRITE_TAC(ARITH :: C1092MPAPO_ROT_ELS);;

(* Lean: all_missing_origins *)
let C1092MPAPO_ALL_MISSING_ORIGINS =
  let one i =
    c1092mpapo_rot_tac "" i THEN
    c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" i THEN DISCH_TAC THEN
    c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" i THEN DISCH_TAC THEN
    c1092mpapo_rot_use C1092MPAPO_MISSING_FORWARD_ROTATED "" i THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpapo_ordinary] o
      check (fun th -> c1092mpapo_head `c1092mpapo_ordinary` th &&
                       hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
    MP_TAC(SPECL (c1092mpapo_d4 "" @ [`l:real`]) C1092MPAWR_BOTTOM_ORDINARY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL (c1092mpapo_d4 "" @ [`l:real`]) C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN
    ASM_REWRITE_TAC[] THEN
    c1092mpapo_pull_tac (c1092mpapo_d4 "") (el i C1092MPAPO_ROTS) [9] in
  prove
   (parse_term (Printf.sprintf "!%s. %s /\\ c1092mpapo_missingForward %s ==> %s /\\ %s /\\ %s /\\ %s"
      C1092AE_P C1092MPAPO_HYPS C1092AE_P
      (c1092mpapo_in 9 "&2" "&1") (c1092mpapo_in 10 "&3" "&2")
      (c1092mpapo_in 11 "&2" "&3") (c1092mpapo_in 8 "&1" "&2")),
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL [one 0; one 1; one 2; one 3]);;

let C1092MPAPO_ORDERS = Printf.sprintf "(!i d1 d2 e1 e2. i < 4 /\\ %s ==> &4 < lcx %s + lcy %s)"
  c1092mpapo_dpk (c1092ae_own "d1 d2 e1 e2 l" 9) (c1092ae_own "d1 d2 e1 e2 l" 8);;

(* Lean: rotated_orders_impossible *)
let C1092MPAPO_ROTATED_ORDERS_IMPOSSIBLE =
  let one orders i =
    let k = string_of_int i in
    let d4 = c1092mpapo_d4 k and g = el i C1092MPAPO_ROTS in
    c1092mpapo_rot_tac k i THEN
    MP_TAC(SPECL (mk_small_numeral i :: d4) orders) THEN
    REWRITE_TAC(ARITH :: C1092MPAPO_ROT_ELS) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun j ->
      MP_TAC(SPECL ([g] @ C1092MPAPO_V4 @ [`l:real`] @ d4 @ [mk_small_numeral j]) C1092OT_OWNERS_TRANSPORT) THEN
      ASM_REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), mk_small_numeral j));
                  c1092ot_pull; c1092ot_px; c1092ot_py; c1092ot_psw; I_THM; PAIR_EQ] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th])) [9; 8] in
  prove
   (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> F" C1092AE_P C1092AE_HYP C1092MPAPO_ORDERS),
    REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> let [np; img; orders] = CONJUNCTS th in
      ASSUME_TAC np THEN ASSUME_TAC img THEN
      MAP_EVERY (one orders) [0; 1; 2; 3]) THEN
    MAP_EVERY (fun k -> MP_TAC(SPECL (C1092MPPE_V @ [parse_term (Printf.sprintf "EL %d c1092wc_code" k)]) OO_UNIT))
      [8; 9; 10; 11] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* per-rotation facts of the pulled packing for a general i < 4 *)
let C1092MPAPO_DGEN_TAC =
  SUBGOAL_THEN `NPACK d1 d2 e1 e2 l` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN
    MAP_EVERY EXISTS_TAC (`EL i c1092mpapo_rotation` :: C1092MPAPO_V4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC (`EL i c1092mpapo_rotation` :: C1092MPAPO_V4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPPE_V @ c1092mpapo_d4 "" @ [`i:num`]) C1092MPAPO_ROTATION_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ c1092mpapo_d4 "" @ [`i:num`]) C1092MPAPO_ORDINARY_ROTATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;
let C1092MPAPO_CEX = "?cC sC uC vC aC. cC * cC + sC * sC = &1 /\\ &0 < aC /\\ ";;

(* Lean: all_missing_positive_impossible *)
let C1092MPAPO_ALL_MISSING_POSITIVE_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ c1092mpapo_missingForward %s /\\
      (!i d1 d2 e1 e2. i < 4 /\\ %s ==> %s c1092psa_frame d1 d2 e1 e2 l cC sC uC vC aC /\\ c977cc_normal cC sC)
      ==> F" C1092AE_P C1092MPAPO_HYPS C1092AE_P c1092mpapo_dpk C1092MPAPO_CEX),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpapo_use C1092MPAPO_ALL_MISSING_ORIGINS THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPAPO_ROTATED_ORDERS_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`] o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cC:real` (X_CHOOSE_THEN `sC:real` (X_CHOOSE_THEN `uC:real`
    (X_CHOOSE_THEN `vC:real` (X_CHOOSE_THEN `aC:real` STRIP_ASSUME_TAC))))) THEN
  C1092MPAPO_DGEN_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ c1092mpapo_d4 "" @ [`i:num`]) C1092MPAPO_MISSING_FORWARD_ROTATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (c1092mpapo_din 8 "&1" "&2")) ASSUME_TAC THENL
   [C1092MPAPO_ENUM_TAC THEN c1092mpapo_gpull_tac [8] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC (SPECL (c1092mpapo_d4 "" @ [`l:real`] @ C1092MPAPO_CV) C1092MPAPO_MISSING_ORDER) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: SectorEntrance (structure) *)
let c1092mpapo_entrance = new_definition (parse_term (Printf.sprintf
  "c1092mpapo_entrance (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                       (cC:real) (sC:real) (uC:real) (vC:real) (aC:real) <=>
     c1092psa_frame c1 c2 a b l cC sC uC vC aC /\\ c977cc_normal cC sC /\\ &0 < sC /\\
     %s /\\ %s /\\ (%s ==> C1092WPS_half cC sC <= &1 / &4)"
  (c1092mpapo_in 8 "&1" "&2") (c1092mpapo_in 5 "&2" "&3 / &2") (c1092mpapo_in 4 "&87 / &50" "&2")));;

(* Lean: impossible_of_positive_entrance *)
let C1092MPAPO_IMPOSSIBLE_OF_POSITIVE_ENTRANCE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\
      (!i d1 d2 e1 e2. i < 4 /\\ %s ==> %s c1092mpapo_entrance d1 d2 e1 e2 l cC sC uC vC aC)
      ==> F" C1092AE_P C1092MPAPO_HYPS c1092mpapo_dpk C1092MPAPO_CEX),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPAPO_ROTATED_ORDERS_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`] o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cC:real` (X_CHOOSE_THEN `sC:real` (X_CHOOSE_THEN `uC:real`
    (X_CHOOSE_THEN `vC:real` (X_CHOOSE_THEN `aC:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpapo_entrance] o
    check (c1092mpapo_head `c1092mpapo_entrance`)) THEN
  C1092MPAPO_DGEN_TAC THEN
  MATCH_MP_TAC (SPECL (c1092mpapo_d4 "" @ [`l:real`] @ C1092MPAPO_CV) C1092MPAPO_SECTOR_ORDER) THEN
  ASM_REWRITE_TAC[]);;
