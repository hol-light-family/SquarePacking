(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardPredecessor.lean         *)
(* (N12Compact.C1092MPPMActualInward).  Actual opposite-inward producers for *)
(* the two OIOI endings.  (Lean header: "Source only".)  Conventions of      *)
(* CP_C1092_MPPMActualInwardSuccessor.ml / MPPMActualInwardFar.ml.           *)
(* g.pullPacking p (g = (F,T,T)) is (d1,d2,e1,e2) with c1092ot_pk g          *)
(* (c1,c2,a,b) = (d1,d2,e1,e2); family / context / owners transport          *)
(* C1092OT_FAMILY_TRANSPORT / C1092CT_CONTEXT_TRANSPORT (via                 *)
(* C1092MMEN_CTX_CONG) / C1092OT_OWNERS_TRANSPORT + C1092CT_INSIDE_PULL.     *)
(* The statements about the pulled packing in opposite_predecessor (outer_   *)
(* owned, successor_profile, the origin and floor of F) are collected in the *)
(* packing-level lemma C1092MPAID_NORTH_SUCCESSOR, applied to the pulled     *)
(* packing.  RigidCharts.opposite F is (cF, sF, --uF - aF, --vF - aF, aF)    *)
(* (C1092RC_INSIDE_OPPOSITE); MissingPredecessor c1092ifm_missingPred;       *)
(* MPPMInwardFinal.right_bar MPPMIF_RIGHT_BAR; inside_segment                *)
(* C1092WC_INSIDE_SEGMENT.  W's unit normal / positive side are returned     *)
(* with the existential.  Tag C1092MPAID_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardSuccessor.ml";;
needs "n12/geometry/CP_C1092_MPPMActualInwardFar.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalMissing.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalRightBar.ml";;
needs "n12/geometry/CP_C1092_RigidCharts.ml";;

(* Lean: successor_origin_floor (private) *)
let C1092MPAID_SUCCESSOR_ORIGIN_FLOOR = prove
 (`forall c s u v a. &1 < a /\ c1092ifsu_negsucc c s u v a /\ ~linside c s u v a (&0) (--(&1))
     ==> --c <= v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092ifsu_negsucc] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `u < --s` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside c s u v a (&0) (--(&1))` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `linside c s u v a (&1 / &2) (--(&1))` THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* the pulled-packing part of opposite_predecessor *)
let C1092MPAID_NORTH_SUCCESSOR = prove
 (parse_term (Printf.sprintf "!%s. %s ==> ?cE sE uE vE aE. %s /\\ %s /\\ c1092ifsu_negsucc cE sE uE vE aE /\\ --cE <= vE"
    C1092AE_P
    (Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ ~%s"
       C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4
       (c1092mpais_in 4 "&1" "&8 / &5") (c1092mpais_in 4 "&2" "&2"))
    (c1092mpais_unit "E") (c1092mpais_frame 5 "E")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 4 "C" THEN c1092mpaif_canon_tac 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIM_OUTER_OWNED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o el 1 o CONJUNCTS o REWRITE_RULE[c1092miff_missing_profile] o
    check (fun th -> can (term_match [] `c1092miff_missing_profile a b c d e`) (concl th))) THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIS_SUCCESSOR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&0` `--(&1)`))
    [c1092moc_excl 5 9 (CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term (c1092mpais_in 9 "&2" "&1"))))] THEN
  SUBGOAL_THEN `&1 < aE` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  MP_TAC(SPECL C1092MPAIS_E C1092MPAID_SUCCESSOR_ORIGIN_FLOOR) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC C1092MPAIS_E THEN ASM_REWRITE_TAC[]);;

let C1092MPAID_G = `(false,true,true)`;;
let C1092MPAID_V4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`];;
let C1092MPAID_D5 = [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`];;

(* the pulled packing g.pullPacking p with its family and wall context *)
let C1092MPAID_SETUP_TAC =
  let g = C1092MPAID_G and v4 = C1092MPAID_V4 in
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
    ALL_TAC];;

(* rewrite the goal's insides of pulled owner i into original owners *)
let c1092mpaid_tr_tac i =
  let g = C1092MPAID_G in
  MP_TAC(SPECL ([g] @ C1092MPAID_V4 @ [`l:real`] @ fst (chop_list 4 C1092MPAID_D5) @ [mk_small_numeral i])
    C1092OT_OWNERS_TRANSPORT) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]) THEN
  REWRITE_TAC[c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), mk_small_numeral i))] THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV);;

let C1092MPAID_OPP_HYPS = Printf.sprintf "%s /\\ %s /\\ (%s /\\ %s) /\\ ~(%s /\\ %s) /\\ %s /\\ ~%s /\\ %s"
  C1092AE_HYP C1092MPPE_CTX (c1092mpais_in 6 "&2" "&113 / &50") (c1092mpais_in 6 "&113 / &50" "&2")
  (c1092mpais_in 6 "&3" "&113 / &50") (c1092mpais_in 6 "&3" "&12 / &5") (c1092mpais_in 6 "&3" "&12 / &5")
  (c1092mpais_in 6 "&2" "&2") (c1092mpais_frame 4 "C");;

let C1092MPAID_W = [`cE:real`; `sE:real`; `--uE - aE`; `--vE - aE`; `aE:real`];;
let C1092MPAID_OPP_ARITH = REAL_ARITH `forall x. &4 - (&2 + --x) = &2 + x`;;

(* Lean: opposite_predecessor *)
let C1092MPAID_OPPOSITE_PREDECESSOR = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> ?cW sW uW vW aW. %s /\\ %s /\\ c1092ifm_missingPred cC sC uC vC aC cW sW uW vW aW"
    C1092AE_P C1092MPAID_OPP_HYPS (c1092mpais_unit "W") (c1092mpais_frame 7 "W")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) && is_conj (rand (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MPAID_SETUP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ ~%s"
      (c1092ae_own "d1 d2 e1 e2 l" 4) (c1092ae_own "d1 d2 e1 e2 l" 4)
      (c1092ae_in "d1 d2 e1 e2 l" 4 "&1" "&8 / &5") (c1092ae_in "d1 d2 e1 e2 l" 4 "&2" "&2")))
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcc_inward; c1092mcc_ordinary] THEN c1092mpaid_tr_tac 4 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL C1092MPAID_D5 C1092MPAID_NORTH_SUCCESSOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    let rec go vs th = match vs with [] -> STRIP_ASSUME_TAC th | v :: r -> X_CHOOSE_THEN v (go r) th in
    go C1092MPAIS_E th) THEN
  SUBGOAL_THEN (list_mk_comb(`c1092mpai_frame`, C1092MPPE_V @ [`7`] @ C1092MPAID_W)) ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[c1092mpai_frame] o check (c1092mpais_frame_of "E")) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[c1092mpai_frame; C1092RC_INSIDE_OPPOSITE; CONJUNCT1 th; CONJUNCT2 th]) THEN
    c1092mpaid_tr_tac 5 THEN REWRITE_TAC[C1092MPAID_OPP_ARITH];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`4`; `7`] @ C1092MPAIS_C @ C1092MPAID_W) C1092MPAI_FRAME_APART) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC C1092MPAID_W THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (fun th -> can (term_match [] `c1092ifsu_negsucc a b c d e`) (concl th))) THEN
  REWRITE_TAC[c1092ifm_missingPred; C1092RC_INSIDE_OPPOSITE; REAL_NEG_NEG] THEN
  ASM_REWRITE_TAC[] THEN c1092mpaif_close_tac);;

(* Lean: inward_right_bar *)
let C1092MPAID_INWARD_RIGHT_BAR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> !y. --(&36 / &85) <= y ==> y <= &0 ==> %s"
    C1092AE_P C1092MPAI_HYPS (c1092mpais_in 6 "&3" "&12 / &5") (c1092mpais_in 6 "&113 / &50" "&2")
    (string_of_term (c1092mpai_chin "10" `&1` `y:real`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAI_RIGHT_ORIGIN THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM IMP_CONJ] THEN
  CONV_TAC C1092MOC_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN
  MATCH_MP_TAC (SPECL (c1092moc_own 10 @ c1092moc_own 6) MPPMIF_RIGHT_BAR) THEN
  ASM_REWRITE_TAC[c1092moc_unit 10; c1092moc_side (); c1092moc_seed 10 (`&1543 / &500`, `&2`); ldisj;
                  c1092moc_apart 10 6] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092moc_box 10))) THEN
  REAL_ARITH_TAC);;

(* Lean: inward_bottom_long_bar *)
let C1092MPAID_INWARD_BOTTOM_LONG_BAR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> !x. --(&14 / &25) <= x ==> x <= &0 ==> %s"
    C1092AE_P C1092MPAI_HYPS (c1092mpais_in 9 "&2" "&1")
    (string_of_term (c1092mpai_chin "9" `x:real` `--(&1)`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092MIN_BOTTOM_FAR THEN DISCH_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  let t = `&25 / &14 * (x + &14 / &25)` in
  MP_TAC(ISPECL ((map parse_term
    ["ooc c1 c2 a b l (EL 9 c1092wc_code)"; "oos c1 c2 a b l (EL 9 c1092wc_code)";
     "oou c1 c2 a b l (EL 9 c1092wc_code)"; "oov c1 c2 a b l (EL 9 c1092wc_code)"; "l:real";
     "&36 / &25"; "&1"; "&2"; "&1"]) @ [t]) C1092WC_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`--(&14 / &25) <= x`; `x <= &0`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(&1 - &25 / &14 * (x + &14 / &25)) * &36 / &25 + (&25 / &14 * (x + &14 / &25)) * &2 = &2 + x`;
              REAL_ARITH `(&1 - t) * &1 + t * &1 = &1`]);;
