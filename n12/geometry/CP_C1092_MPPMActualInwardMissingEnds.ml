(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardMissingEnds.lean         *)
(* (N12Compact.C1092MPPMActualInward).  Actual missing-center inward         *)
(* endings.  (Lean header: "Source only, uncompiled".)  Conventions of       *)
(* CP_C1092_MPPMActualInwardPositiveMissing.ml / MPPMActualInwardOIOI.ml:    *)
(* owners p i at mask EL i c1092wc_code (side l); Frame p i C is             *)
(* c1092mpai_frame c1 c2 a b l i cC sC uC vC aC (C's unit normal / positive  *)
(* side explicit); chart p i the tuple c1092mpai_chart i.  NorthInward /     *)
(* NorthOrdinary c1092mais_northInward / c1092mais_northOrdinary,            *)
(* north_cover C1092MAIS_NORTH_COVER; positive_missing_input /               *)
(* opposite_inward_left_origin / left_seed_points C1092MPAIPM_*;             *)
(* MPPMInwardPositive.origin_impossible C1092IPOE_ORIGIN_IMPOSSIBLE,         *)
(* far_impossible C1092IPFE_FAR_IMPOSSIBLE; ordinary_opposite_bar            *)
(* C1092MPAIF_ORDINARY_OPPOSITE_BAR; outer_omitted_input                     *)
(* C1092MPAIM_OUTER_OMITTED_INPUT; MPPMInwardSmallThree.Input /              *)
(* impossible c1092istd_input / C1092ISTE_IMPOSSIBLE; successor_profile      *)
(* C1092MPAIS_SUCCESSOR_PROFILE.  Tag C1092MAIME_.                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardPositiveMissing.ml";;
needs "n12/geometry/CP_C1092_MPPMActualInwardSymmetry.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveOriginEnding.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveFarEnding.ml";;
needs "n12/geometry/CP_C1092_MPPMActualInwardFar.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardSmallThreeEnding.ml";;

(* Frame.apart of square n (frame i) and chart j, in either order *)
let c1092maime_apart_tac i n j swap =
  let sq = c1092mpais_sq n and ch = c1092mpai_chart (string_of_int j) in
  let ii = mk_small_numeral i and jj = mk_small_numeral j in
  MP_TAC(SPECL (C1092MPPE_V @ (if swap then [jj; ii] @ ch @ sq else [ii; jj] @ sq @ ch)) C1092MPAI_FRAME_APART) THEN
  ASM_REWRITE_TAC[SPECL (C1092MPPE_V @ [jj]) C1092MPAI_CHART_FRAME; ARITH] THEN
  DISCH_TAC;;

let C1092MAIME_POS_HYPS = Printf.sprintf "%s /\\ ~%s /\\ %s /\\ %s /\\ c977cc_normal cC sC"
  C1092MPAIP_BASE (c1092mpais_in 4 "&2" "&2") (c1092mpais_frame 4 "C") (c1092mpais_unit "C");;

(* Lean: positive_missing_origin *)
let C1092MAIME_POSITIVE_MISSING_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ c1092mais_northInward %s ==> F"
    C1092AE_P C1092MAIME_POS_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mais_northInward] THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIPM_POSITIVE_MISSING_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAIPM_OPPOSITE_INWARD_LEFT_ORIGIN THEN DISCH_TAC THEN
  c1092mpais_fact "C" (mk_neg (c1092mpais_cin "C" `--(&1)` `&0`))
    [c1092moc_excl 4 8 (CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term (c1092mpais_in 8 "&1" "&2"))))] THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIS_E) C1092IPOE_ORIGIN_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: positive_missing_far *)
let C1092MAIME_POSITIVE_MISSING_FAR = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s ==> F"
    C1092AE_P C1092MAIME_POS_HYPS C1092MPAIF_OPP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIPM_POSITIVE_MISSING_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAIF_ORDINARY_OPPOSITE_BAR THEN DISCH_TAC THEN
  c1092maime_apart_tac 5 "E" 10 false THEN
  SUBGOAL_THEN (mk_neg (c1092mpais_cin "E" `&1` `--(&14 / &25)`)) ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `--(&14 / &25)`] o REWRITE_RULE[ldisj] o
      check (fun th -> can (term_match [] (list_mk_comb(`ldisj`, C1092MPAIS_E @ C1092MPAIF_CH10))) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--(&14 / &25)` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `EL 10 c1092wc_code`)) (concl th))) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  c1092mpai_use C1092MPAIPM_LEFT_SEED_POINTS THEN STRIP_TAC THEN
  c1092maime_apart_tac 4 "C" 8 false THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIS_E @ c1092mpai_chart "8") C1092IPFE_FAR_IMPOSSIBLE) THEN
  ASM_SIMP_TAC (REAL_LT_IMP_LE :: C1092MPAIF_SIMP));;

(* Lean: nonpositive_missing_omitted *)
let C1092MAIME_NONPOSITIVE_MISSING_OMITTED = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\ ~%s /\\ %s /\\ %s /\\ c977cc_normal cC (--sC) ==> F"
    C1092AE_P C1092MPAIP_BASE (c1092mpais_in 4 "&2" "&2") (c1092mpais_in 4 "&1" "&8 / &5")
    (c1092mpais_frame 4 "C") (c1092mpais_unit "C")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIM_OUTER_OMITTED_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIS_SUCCESSOR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mpais_apart_tac 4 "C" 5 "E" THEN
  c1092maime_apart_tac 5 "E" 9 true THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIM_CH9 @ C1092MPAIS_E) C1092ISTE_IMPOSSIBLE) THEN
  REWRITE_TAC[c1092istd_input] THEN
  ASM_SIMP_TAC (REAL_LT_IMP_LE :: C1092MPAIF_SIMP) THEN c1092mpaif_close_tac);;

(* Lean: missing_center_outer *)
let C1092MAIME_MISSING_CENTER_OUTER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ ~%s ==> %s"
    C1092AE_P C1092MPAIP_BASE (c1092mpais_in 4 "&2" "&2") (c1092mpais_in 4 "&1" "&8 / &5")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REFUTE_THEN ASSUME_TAC THEN
  c1092mpaif_canon_tac 4 "C" THEN
  ASM_CASES_TAC `&0 <= sC` THENL
   [SUBGOAL_THEN `c977cc_normal cC sC` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs sC <= cC` THEN UNDISCH_TAC `&0 <= sC` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    c1092mpai_use C1092MAIS_NORTH_COVER THEN REWRITE_TAC[c1092mais_northOrdinary] THEN STRIP_TAC THENL
     [MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MAIME_POSITIVE_MISSING_FAR) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MAIME_POSITIVE_MISSING_ORIGIN) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MAIME_NONPOSITIVE_MISSING_OMITTED) THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(&0 <= sC)` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `abs sC <= cC` THEN UNDISCH_TAC `~(&0 <= sC)` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `cC * cC + sC * sC = &1` THEN REAL_ARITH_TAC]]);;
