(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardFar.lean                 *)
(* (N12Compact.C1092MPPMActualInward).  The ordinary-opposite alternatives,  *)
(* with genuine original wall advance.  (Lean header: "Source only".)        *)
(* Conventions of CP_C1092_MPPMActualInwardSuccessor.ml (squares C, E with   *)
(* explicit OpenSquare unit normal / positive side; Frame c1092mpai_frame;   *)
(* chart c1092mpai_chart).  MPPMInwardOuterFar.Input c1092miofo_input,       *)
(* missing_center_impossible / centered_impossible C1092MIOFO_*;             *)
(* MPPMInwardOmittedFar.omitted_lower / Input / impossible C1092IOF_OMITTED_ *)
(* LOWER / c1092iof_input / C1092IOF_IMPOSSIBLE; right_far_no_omission       *)
(* C1092OWA_RIGHT_FAR_NO_OMISSION; WallProfile.vertical_owned                *)
(* OCWPVG_VERTICAL_OWNED.  The Lean structure fields raw.1.normal /          *)
(* raw.1.upperV are fields of c1092miff_missing_profile.  Tag C1092MPAIF_.   *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardSuccessor.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardOuterFar.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardOmittedFar.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryWallAdvance.ml";;

let C1092MPAIF_OPP = c1092mpais_in 6 "&3" "&113 / &50";;
let C1092MPAIF_CH10 = c1092mpai_chart "10";;
let C1092MPAIF_CH10S = c1092mpaim_tuple C1092MPAIF_CH10;;

(* Lean: ordinary_opposite_bar *)
let C1092MPAIF_ORDINARY_OPPOSITE_BAR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> !y. --(&14 / &25) <= y ==> y <= &0 ==> %s"
    C1092AE_P C1092MPAI_HYPS C1092MPAIF_OPP (string_of_term (c1092mpai_chin "10" `&1` `y:real`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092OWA_RIGHT_FAR_NO_OMISSION THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAI_RIGHT_ORIGIN THEN DISCH_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MP_TAC(ISPECL (map parse_term
    ["ooc c1 c2 a b l (EL 10 c1092wc_code)"; "oos c1 c2 a b l (EL 10 c1092wc_code)";
     "oou c1 c2 a b l (EL 10 c1092wc_code)"; "oov c1 c2 a b l (EL 10 c1092wc_code)"; "l:real";
     "&3"; "&36 / &25"; "&2"]) OCWPVG_VERTICAL_OWNED) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  MAP_EVERY UNDISCH_TAC [`--(&14 / &25) <= y`; `y <= &0`] THEN REAL_ARITH_TAC);;

let C1092MPAIF_INPUT_HYPS = Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ %s /\\ %s /\\ abs sE <= cE"
  C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4 C1092MPAIF_OPP (c1092mpais_in 9 "&2" "&1")
  (c1092mpais_frame 4 "C") (c1092mpais_frame 5 "E") (c1092mpais_unit "C") (c1092mpais_unit "E");;

let c1092mpaif_close_tac =
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[IMP_CONJ] THEN FIRST_ASSUM ACCEPT_TAC;
                              C1092MPAIS_SIDES_TAC; RASM_ARITH_TAC];;

(* Lean: outer_far_input *)
let C1092MPAIF_OUTER_FAR_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC cE sE uE vE aE. %s ==> c1092miofo_input cC sC uC vC aC cE sE uE vE aE %s"
    C1092AE_P C1092MPAIF_INPUT_HYPS C1092MPAIF_CH10S),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092MIN_SOUTHWEST_CROSSPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAIF_ORDINARY_OPPOSITE_BAR THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_NEGATIVE_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTRAL_ANCHORS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIS_SUCCESSOR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mpais_apart_tac 4 "C" 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`5`; `10`] @ C1092MPAIS_E @ C1092MPAIF_CH10) C1092MPAI_FRAME_APART) THEN
  ASM_REWRITE_TAC[SPECL (C1092MPPE_V @ [`10`]) C1092MPAI_CHART_FRAME; ARITH] THEN DISCH_TAC THEN
  C1092MPAI_INWARD_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `&0` `--(&13 / &50)`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&1 / &2)` `&0`) [] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&0` `--(&1)`))
    [c1092moc_excl 5 9 (CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term (c1092mpais_in 9 "&2" "&1"))))] THEN
  REWRITE_TAC[c1092miofo_input] THEN ASM_REWRITE_TAC[] THEN c1092mpaif_close_tac);;

(* the canonical frame of owner i as square n in the assumptions *)
let c1092mpaif_canon_tac i n =
  let rec go vs th = match vs with [] -> STRIP_ASSUME_TAC th | v :: r -> X_CHOOSE_THEN v (go r) th in
  MP_TAC(MP (SPECL (C1092MPPE_V @ [mk_small_numeral i]) C1092MPAI_CANONICAL_FRAME)
            (ASSUME `NPACK c1 c2 a b l`)) THEN
  DISCH_THEN(go (c1092mpais_sq n));;
let C1092MPAIF_SIMP = [OO_UNIT; OO_SIDE; REAL_ARITH `&1 < l ==> &0 < l`];;

(* Lean: missing_outer_far *)
let C1092MPAIF_MISSING_OUTER_FAR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ ~%s /\\ %s ==> F"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4
    (c1092mpais_in 4 "&1" "&8 / &5") (c1092mpais_in 4 "&2" "&2") C1092MPAIF_OPP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 4 "C" THEN c1092mpaif_canon_tac 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIM_OUTER_OWNED_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPAIS_C @ C1092MPAIM_CH9) C1092IFOW_OUTER_OWNED_PROFILE) THEN
  ASM_SIMP_TAC C1092MPAIF_SIMP THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIM_OUTER_OWNED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092miff_missing_profile] o
    check (fun th -> can (term_match [] `c1092miff_missing_profile a b c d e`) (concl th))) THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIF_OUTER_FAR_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIS_E @ C1092MPAIF_CH10) C1092MIOFO_MISSING_CENTER_IMPOSSIBLE) THEN
  ASM_SIMP_TAC (REAL_LT_IMP_LE :: C1092MPAIF_SIMP));;

let C1092MPAIF_CENTERED_HYPS outer = Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ %s%s /\\ %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ sC < &0 /\\ %s"
  C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4 (c1092mpais_in 4 "&2" "&2")
  outer (c1092mpais_in 4 "&1" "&8 / &5") C1092MPAIF_OPP (c1092mpais_frame 4 "C") (c1092mpais_unit "C");;
let c1092mpaif_cstmt outer =
  parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> F" C1092AE_P (C1092MPAIF_CENTERED_HYPS outer));;

(* Lean: centered_outer_far *)
let C1092MPAIF_CENTERED_OUTER_FAR = prove
 (c1092mpaif_cstmt "",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTERED_NEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIF_OUTER_FAR_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIS_E @ C1092MPAIF_CH10) C1092MIOFO_CENTERED_IMPOSSIBLE) THEN
  ASM_SIMP_TAC (REAL_LT_IMP_LE :: C1092MPAIF_SIMP));;

(* Lean: centered_omitted_far *)
let C1092MPAIF_CENTERED_OMITTED_FAR = prove
 (c1092mpaif_cstmt "~",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 5 "E" THEN
  C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092MIN_SOUTHWEST_CROSSPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAIF_ORDINARY_OPPOSITE_BAR THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTERED_NEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTRAL_ANCHORS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIS_SUCCESSOR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mpais_apart_tac 4 "C" 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`5`; `10`] @ C1092MPAIS_E @ C1092MPAIF_CH10) C1092MPAI_FRAME_APART) THEN
  ASM_REWRITE_TAC[SPECL (C1092MPPE_V @ [`10`]) C1092MPAI_CHART_FRAME; ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&1 / &2)` `&0`) [] THEN
  c1092mpais_fact "C" (mk_neg (c1092mpais_cin "C" `--(&1)` `--(&2 / &5)`)) [] THEN
  MP_TAC(SPECL C1092MPAIS_C C1092IOF_OMITTED_LOWER) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIS_E @ C1092MPAIF_CH10) C1092IOF_IMPOSSIBLE) THEN
  ASM_SIMP_TAC C1092MPAIF_SIMP THEN
  REWRITE_TAC[c1092iof_input] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN c1092mpaif_close_tac);;

(* Lean: centered_far *)
let C1092MPAIF_CENTERED_FAR = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ sC < &0 /\\ %s ==> F"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4 (c1092mpais_in 4 "&2" "&2")
    C1092MPAIF_OPP (c1092mpais_frame 4 "C") (c1092mpais_unit "C")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term (c1092mpais_in 4 "&1" "&8 / &5")) THENL
   [MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIF_CENTERED_OUTER_FAR);
    MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIF_CENTERED_OMITTED_FAR)] THEN
  ASM_REWRITE_TAC[]);;
