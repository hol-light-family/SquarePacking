(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOnePositiveActual.lean               *)
(* (N12Compact.C1092MPPMOnePositive; Lean header: "Source only").  Actual    *)
(* entrances of the one-positive local lemmas.  Conventions of               *)
(* CP_C1092_MPPMAllNonpositiveActual.ml (ActualFrame c1092psa_frame;         *)
(* rotation-1 packing d1 d2 e1 e2 (C1092MAR_DPK1), rotation-3 packing        *)
(* d13 d23 e13 e23; clockwise D = (cD, sD, --vD - aD, uD, aD); (owners pk 9) *)
(* .translated 2 2 = c1092nopa_tr pk 9).  PositiveMissingInput c1092opc_input*)
(* / positive_missing_impossible C1092OPME_POSITIVE_MISSING_IMPOSSIBLE;      *)
(* RetainingPairInput c1092opra_input; retaining_successor_impossible        *)
(* C1092OPRE_*; missing_positive_data C1092MABO_*; MissingPositiveBoundaries *)
(* .profile C1092MPBP_PROFILE; narrow_of_positive_predecessor C1092PNRA_*;   *)
(* narrow_of_missing_predecessor C1092NPPA_*; next_forward_iff /             *)
(* nonpositive_retaining_crosspoint C1092MACR_*; next_crosspoint             *)
(* C1092MAPC_NEXT_CROSSPOINT.  The private marker_point is oo_seed.          *)
(* Tag C1092OPAC_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMOnePositiveMissingEnding.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveNegativeRetainingActual.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessorActual.ml";;
needs "n12/geometry/CP_C1092_MPPMOnePositiveRetainingEnding.ml";;
needs "n12/geometry/CP_C1092_MPPMActualCrosspoints.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveActual.ml";;

(* Lean: marker_point (private) *)
let C1092OPAC_MARKER_POINT = C1092PSA_MARKER_POINT;;

let C1092OPAC_ROT1_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK1)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,true,false)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 1 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 1 THEN DISCH_TAC;;

let C1092OPAC_NARROW = "&97 / &100 < cC /\\ &4 * --sC < cC /\\ vC + aC < &43 / &500";;
let C1092OPAC_PM_HYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\
      c977cc_normal cD sD /\\ &0 < sD /\\ ~%s /\\ %s"
  C1092NFA_NHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092OPAC_NARROW C1092MAR_DPK1 C1092MAR_DSQ
  (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 5 "&2" "&3 / &2");;

(* Lean: actual_positive_missing_input *)
let C1092OPAC_ACTUAL_POSITIVE_MISSING_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> c1092opc_input cC sC uC vC aC cD sD (--vD - aD) uD aD %s"
    C1092AE_P C1092OPAC_PM_HYPS (c1092nopa_trs C1092MAR_V 9)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  c1092anpa_bar_tac C1092MAR_V C1092MAR_CV THEN
  C1092OPAC_ROT1_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092ae_in "d1 d2 e1 e2 l" 4 "&87 / &50" "&2"))) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [4] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MABO_MISSING_POSITIVE_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  c1092anpa_side_tac `d1:num->real` `aD:real` THEN
  MP_TAC(SPECL C1092MAR_DV C1092MPBP_PROFILE) THEN ASM_REWRITE_TAC[c1092mpbp_profile] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj cC sC uC vC aC %s /\\ ldisj cC sC uC vC aC cD sD (--vD - aD) uD aD"
      (c1092nopa_trs C1092MAR_V 9))) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
    c1092anpa_freq `c1:num->real` THENL
     [c1092anpa_apart_tac C1092MAR_V 4 9;
      c1092anpa_seq `c1:num->real` THEN c1092anpa_apart_tac C1092MAR_V 4 5];
    ALL_TAC] THEN
  REWRITE_TAC[c1092opc_input] THEN ASM_REWRITE_TAC[c1092mcbh_half; GSYM C1092WPS_half] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
  REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  c1092anpa_seq `c1:num->real` THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 5 (`&47 / &20`, `&33 / &20`)] THEN ASM_REWRITE_TAC[]);;

(* Lean: positive_missing_of_narrow *)
let C1092OPAC_POSITIVE_MISSING_OF_NARROW = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s ==> F"
    C1092AE_P C1092OPAC_PM_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092OPAC_ACTUAL_POSITIVE_MISSING_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ C1092MAR_E @ c1092nopa_tr C1092MAR_V 9) C1092OPME_POSITIVE_MISSING_IMPOSSIBLE) THEN
  MP_TAC(SPECL (C1092MAR_V @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

let C1092OPAC_W = c1092anpa_sq "W";;
let C1092OPAC_D3 = c1092anpa_d "3";;
let C1092OPAC_WPK = Printf.sprintf "%s /\\ %s /\\ %s" (c1092anpa_pk 3 C1092MPAPO_V4 "3")
  (c1092anpa_sqh "W") (c1092anpa_fr "3" "W");;
let C1092OPAC_TAIL = Printf.sprintf "%s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD"
  C1092MAR_DPK1 C1092MAR_DSQ;;

(* Lean: positive_sandwich_impossible *)
let C1092OPAC_POSITIVE_SANDWICH_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d13 d23 e13 e23 cW sW uW vW aW d1 d2 e1 e2 cD sD uD vD aD.
      %s /\\ %s /\\ %s /\\ c977cc_normal cW sW /\\ &0 < sW /\\ %s /\\ c977cc_normal cD sD /\\ &0 < sD /\\
      ~%s /\\ %s ==> F"
    C1092AE_P C1092NFA_NHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092OPAC_WPK C1092OPAC_TAIL
    (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 5 "&2" "&3 / &2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092OPAC_D3 @ C1092OPAC_W) C1092PNRA_NARROW_OF_POSITIVE_PREDECESSOR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092OPAC_POSITIVE_MISSING_OF_NARROW) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: missing_predecessor_positive_impossible *)
let C1092OPAC_MISSING_PREDECESSOR_POSITIVE_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d13 d23 e13 e23 cW sW uW vW aW d1 d2 e1 e2 cD sD uD vD aD.
      %s /\\ %s /\\ %s /\\ c977cc_normal cW (--sW) /\\ ~%s /\\ %s /\\ c977cc_normal cD sD /\\ &0 < sD /\\
      ~%s /\\ %s ==> F"
    C1092AE_P C1092NFA_NHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092OPAC_WPK (c1092mppe_in 7 "&2" "&113 / &50")
    C1092OPAC_TAIL (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 5 "&2" "&3 / &2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092OPAC_D3 @ C1092OPAC_W) C1092NPPA_NARROW_OF_MISSING_PREDECESSOR) THEN
  ASM_REWRITE_TAC[c1092ansh_shallow] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092OPAC_POSITIVE_MISSING_OF_NARROW) THEN
  ASM_REWRITE_TAC[]);;

let C1092OPAC_RN_HYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cD (--sD) /\\ %s /\\ %s"
  C1092NFA_NHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092OPAC_NARROW C1092OPAC_TAIL
  (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 6 "&5 / &2" "&2");;

(* Lean: retaining_of_narrow *)
let C1092OPAC_RETAINING_OF_NARROW = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s ==> F"
    C1092AE_P C1092OPAC_RN_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D) C1092MACR_NEXT_FORWARD_IFF) THEN
  ASM_REWRITE_TAC[c1092mapc_forward] THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mppe_in 5 "&5 / &2" "&2"))) ASSUME_TAC THENL
   [c1092mpapo_excl_tac 5 6 `&5 / &2` `&2`; ALL_TAC] THEN
  C1092OPAC_ROT1_TAC THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  c1092anpa_bar_tac (c1092anpa_d5 "") C1092MAR_DV THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[c1092mar_successorFrame] o
    check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  SUBGOAL_THEN `~linside cD sD uD vD aD (&0) (--(&1 / &2))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM C1092MEA_INSIDE_CLOCKWISE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj cD sD uD vD aD %s /\\ ldisj cC sC uC vC aC cD sD (--vD - aD) uD aD"
      (c1092nopa_trs (c1092anpa_d5 "") 9))) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED] THENL
     [c1092anpa_freq `d1:num->real` THEN c1092anpa_apart_tac (c1092anpa_d5 "") 4 9;
      c1092anpa_freq `c1:num->real` THEN ASM_REWRITE_TAC[] THEN c1092anpa_apart_tac C1092MAR_V 4 5];
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ C1092MAR_DV @ c1092nopa_tr (c1092anpa_d5 "") 9)
    C1092OPRE_RETAINING_SUCCESSOR_IMPOSSIBLE) THEN
  MP_TAC(SPECL (c1092anpa_d5 "" @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[c1092opra_input] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
  REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  C1092MPAPO_ORD_TAC THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 5 (`&47 / &20`, `&33 / &20`)] THEN ASM_REWRITE_TAC[]);;

(* Lean: missing_predecessor_retaining_impossible *)
let C1092OPAC_MISSING_PREDECESSOR_RETAINING_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d13 d23 e13 e23 cW sW uW vW aW d1 d2 e1 e2 cD sD uD vD aD.
      %s /\\ %s /\\ %s /\\ c977cc_normal cW (--sW) /\\ ~%s /\\ %s /\\ c977cc_normal cD (--sD) /\\ %s /\\ %s ==> F"
    C1092AE_P C1092NFA_NHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092OPAC_WPK (c1092mppe_in 7 "&2" "&113 / &50")
    C1092OPAC_TAIL (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 6 "&5 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092OPAC_D3 @ C1092OPAC_W) C1092NPPA_NARROW_OF_MISSING_PREDECESSOR) THEN
  ASM_REWRITE_TAC[c1092ansh_shallow] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092OPAC_RETAINING_OF_NARROW) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: positive_predecessor_retaining_impossible *)
let C1092OPAC_POSITIVE_PREDECESSOR_RETAINING_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d13 d23 e13 e23 cW sW uW vW aW d1 d2 e1 e2 cD sD uD vD aD.
      %s /\\ %s /\\ %s /\\ c977cc_normal cW sW /\\ &0 < sW /\\ %s /\\ c977cc_normal cD (--sD) /\\ %s /\\ %s ==> F"
    C1092AE_P C1092NFA_NHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092OPAC_WPK
    C1092OPAC_TAIL (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 6 "&5 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D) C1092MACR_NEXT_FORWARD_IFF) THEN
  ASM_REWRITE_TAC[c1092mapc_forward] THEN DISCH_TAC THEN
  c1092mapc_facts_tac C1092MPAPO_V4 C1092MAR_D `1` THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MACR_NONPOSITIVE_RETAINING_CROSSPOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D) C1092MAPC_NEXT_CROSSPOINT) THEN
  ASM_REWRITE_TAC[c1092mapc_crosspoint] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092OPAC_D3 @ C1092OPAC_W) C1092PNRA_NARROW_OF_POSITIVE_PREDECESSOR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092OPAC_RETAINING_OF_NARROW) THEN
  ASM_REWRITE_TAC[]);;
