(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardOIOI.lean                *)
(* (N12Compact.C1092MPPMActualInward).  The two completed OIOI endings,      *)
(* joined to their original owners.  (Lean header: "Source only,            *)
(* uncompiled".)  Conventions of CP_C1092_MPPMActualInwardPredecessor.ml /   *)
(* MPPMActualInwardSuccessor.ml: owners p i at mask EL i c1092wc_code (side  *)
(* l); Frame p i C is c1092mpai_frame c1 c2 a b l i cC sC uC vC aC (C's      *)
(* OpenSquare unit normal / positive side explicit); chart p i the tuple     *)
(* c1092mpai_chart i.  opposite_predecessor C1092MPAID_OPPOSITE_PREDECESSOR; *)
(* canonical_frame C1092MPAI_CANONICAL_FRAME; centered_input /               *)
(* successor_profile / negative_faces C1092MPAIS_*; centered_half_angle      *)
(* C1092IFA_CENTERED_HALF_ANGLE; CenteredPredecessor                         *)
(* c1092mifp_centeredPredecessor; centered_impossible                        *)
(* C1092IFC_CENTERED_IMPOSSIBLE; outer_owned C1092MPAIM_OUTER_OWNED;         *)
(* missing_impossible C1092IFM_MISSING_IMPOSSIBLE; inward_right_bar /        *)
(* inward_bottom_long_bar C1092MPAID_*; bottom_corner C1092MPAI_BOTTOM_CORNER;*)
(* Frame.apart C1092MPAI_FRAME_APART.  Tag C1092MPAIO_.                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardPredecessor.ml";;

let C1092MPAIO_NORTH = Printf.sprintf "(%s /\\ %s) /\\ ~(%s /\\ %s) /\\ %s"
  (c1092mpais_in 6 "&2" "&113 / &50") (c1092mpais_in 6 "&113 / &50" "&2")
  (c1092mpais_in 6 "&3" "&113 / &50") (c1092mpais_in 6 "&3" "&12 / &5") (c1092mpais_in 6 "&3" "&12 / &5");;

(* Frame.apart of square n (frame i) and chart j *)
let c1092mpaio_chart_apart_tac i n j =
  MP_TAC(SPECL (C1092MPPE_V @ [mk_small_numeral i; mk_small_numeral j] @ c1092mpais_sq n @
                c1092mpai_chart (string_of_int j)) C1092MPAI_FRAME_APART) THEN
  ASM_REWRITE_TAC[SPECL (C1092MPPE_V @ [mk_small_numeral j]) C1092MPAI_CHART_FRAME; ARITH] THEN
  DISCH_TAC;;

let c1092mpaio_strip_def pat def =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[def] o
    check (fun th -> can (term_match [] pat) (concl th)));;

let c1092mpaio_choose vs =
  DISCH_THEN(fun th ->
    let rec go vs th = match vs with [] -> STRIP_ASSUME_TAC th | v :: r -> X_CHOOSE_THEN v (go r) th in
    go vs th);;

(* Lean: centered_oioi *)
let C1092MPAIO_CENTERED_OIOI = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ sC < &0 ==> F"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4 (c1092mpais_in 4 "&2" "&2")
    C1092MPAIO_NORTH (c1092mpais_frame 4 "C") (c1092mpais_unit "C")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mpais_in 6 "&2" "&2"))) ASSUME_TAC THENL
   [MP_TAC(SPECL (C1092MPPE_V @ [`4`; `6`]) C1092WC_OWNERS_DISJOINT) THEN
    ASM_REWRITE_TAC[ldisj; ARITH] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&2`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAID_OPPOSITE_PREDECESSOR) THEN
  ASM_REWRITE_TAC[] THEN c1092mpaio_choose C1092MPAIS_W THEN
  c1092mpaif_canon_tac 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E @ C1092MPAIS_W) C1092MPAIS_CENTERED_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpaio_strip_def `c1092ifm_missingPred a b c d e f g h i j` c1092ifm_missingPred THEN
  SUBGOAL_THEN `abs sW <= cW` ASSUME_TAC THENL
   [MP_TAC(SPECL [`cW:real`; `--sW`] C977CC_NORMAL_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c977cc_normal cW (--sW)` THEN REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPAIS_C @ C1092MPAIS_W) C1092IFA_CENTERED_HALF_ANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIS_SUCCESSOR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_NEGATIVE_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAI_BOTTOM_CORNER THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAID_INWARD_RIGHT_BAR THEN DISCH_TAC THEN
  c1092mpais_apart_tac 4 "C" 5 "E" THEN
  c1092mpaio_chart_apart_tac 5 "E" 10 THEN
  c1092mpaio_chart_apart_tac 4 "C" 0 THEN
  c1092mpaio_chart_apart_tac 5 "E" 9 THEN
  C1092MPAI_INWARD_TAC THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `&0` `--(&13 / &50)`) [] THEN
  SUBGOAL_THEN `c1092mifp_centeredPredecessor cC sC uC vC aC cW sW uW vW aW` ASSUME_TAC THENL
   [c1092mpaio_strip_def `c1092ifh_capInput a b c d e f g h i j` c1092ifh_capInput THEN
    REWRITE_TAC[c1092mifp_centeredPredecessor] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIS_W @ C1092MPAIS_E @ c1092mpai_chart "10" @
                       c1092mpai_chart "9" @ c1092mpai_chart "0") C1092IFC_CENTERED_IMPOSSIBLE) THEN
  ASM_SIMP_TAC (REAL_LT_IMP_LE :: C1092MPAIF_SIMP) THEN c1092mpaif_close_tac);;

(* Lean: opposed_missing_oioi *)
let C1092MPAIO_OPPOSED_MISSING_OIOI = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ ~%s /\\ %s /\\ ~%s ==> F"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4
    (c1092mpais_in 4 "&1" "&8 / &5") (c1092mpais_in 4 "&2" "&2") C1092MPAIO_NORTH
    (c1092mpais_in 6 "&2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 4 "C" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIM_OUTER_OWNED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAID_OPPOSITE_PREDECESSOR) THEN
  ASM_REWRITE_TAC[] THEN c1092mpaio_choose C1092MPAIS_W THEN
  c1092mpaif_canon_tac 5 "E" THEN
  FIRST_ASSUM(ASSUME_TAC o el 1 o CONJUNCTS o REWRITE_RULE[c1092miff_missing_profile] o
    check (fun th -> can (term_match [] `c1092miff_missing_profile a b c d e`) (concl th))) THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIS_SUCCESSOR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAID_INWARD_BOTTOM_LONG_BAR THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAID_INWARD_RIGHT_BAR THEN DISCH_TAC THEN
  c1092mpaio_chart_apart_tac 4 "C" 9 THEN
  c1092mpais_apart_tac 4 "C" 5 "E" THEN
  c1092mpaio_chart_apart_tac 5 "E" 10 THEN
  c1092mpaio_chart_apart_tac 5 "E" 9 THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIS_W @ C1092MPAIS_E @ c1092mpai_chart "9" @
                       c1092mpai_chart "10") C1092IFM_MISSING_IMPOSSIBLE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `--(&14 / &25) = --(&14) / &25`]) THEN
  ASM_SIMP_TAC (REAL_LT_IMP_LE :: C1092MPAIF_SIMP) THEN c1092mpaif_close_tac);;
