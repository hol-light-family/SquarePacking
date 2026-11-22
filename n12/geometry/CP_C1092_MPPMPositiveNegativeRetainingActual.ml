(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveNegativeRetainingActual.lean *)
(* (N12Compact.C1092MPPMPositiveNegativeRetaining; Lean header: "Source      *)
(* only, uncompiled").  Literal Corollary 2 of POSITIVE-NEGATIVE-RETAINING-  *)
(* SHALLOW.  Conventions of CP_C1092_MPPMActualRetaining.ml (owners p i at   *)
(* mask EL i c1092wc_code; ActualFrame c1092psa_frame; (rotation i)          *)
(* .pullPacking p = (d1,d2,e1,e2) with c1092ot_pk (EL i c1092mpapo_rotation);*)
(* SuccessorFrame c1092mar_successorFrame; MMMPEndingAxes.clockwise D =      *)
(* (cD, sD, --vD - aD, uD, aD)).  (owners p 10).translated 2 2 is            *)
(* c1092mabo_tr 10 (C1092PSA_INSIDE_TRANSLATED).  Input / Profile:           *)
(* c1092pnrsup_input / c1092pnrsup_profile, profile C1092PNR_PROFILE;        *)
(* ActualNonpositive.bottom_origin / actual_core C1092MANC_*; positive_faces *)
(* C1092MABO_POSITIVE_FACES; successor_faces C1092ANC_SUCCESSOR_FACES;       *)
(* vertical_segment OO_VERTICAL_SEGMENT.  The private marker_point is oo_seed*)
(* (c1092psa_seed).  Tag C1092PNRA_.                                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMPositiveNegativeRetaining.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonpositiveCore.ml";;
needs "n12/geometry/CP_C1092_MPPMActualRetaining.ml";;

(* Lean: marker_point (private) *)
let C1092PNRA_MARKER_POINT = C1092PSA_MARKER_POINT;;

(* the rotation-1 packing (d1,d2,e1,e2) with its NPACK / IMAGE / context / Ordinary *)
let C1092PNRA_ROT1_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK1)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,true,false)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 1 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 1 THEN DISCH_TAC;;

let C1092PNRA_DHYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD (--sD)"
  C1092MPAPO_HYPS C1092MAR_DPK1 C1092MAR_DSQ;;

(* Lean: actual_right_bar *)
let C1092PNRA_ACTUAL_RIGHT_BAR = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2 cD sD uD vD aD y. %s /\\ --(&14 / &25) <= y /\\ y <= &0 ==> %s"
    C1092AE_P C1092PNRA_DHYPS (c1092mppe_in 10 "&3" "&2 + y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  C1092PNRA_ROT1_TAC THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MANC_BOTTOM_ORIGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [9] THEN DISCH_TAC THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&2`] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

let C1092PNRA_R = String.concat " " (map (fun t -> "(" ^ string_of_term t ^ ")") (c1092mabo_tr 10));;
let C1092PNRA_IHYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\
      c977cc_normal cD (--sD) /\\ %s /\\ %s"
  C1092MABO_PHYPS C1092MAR_DPK1 C1092MAR_DSQ (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 6 "&5 / &2" "&2");;

(* Lean: actual_input *)
let C1092PNRA_ACTUAL_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> c1092pnrsup_input cC sC uC vC aC cD sD (--vD - aD) uD aD %s"
    C1092AE_P C1092PNRA_IHYPS C1092PNRA_R),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "!y. --(&14 / &25) <= y ==> y <= &0 ==> %s"
      (c1092mppe_in 10 "&3" "&2 + y"))) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092PNRA_ACTUAL_RIGHT_BAR) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_POSITIVE_FACES) THEN
  ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mppe_in 5 "&5 / &2" "&2"))) ASSUME_TAC THENL
   [c1092mpapo_excl_tac 5 6 `&5 / &2` `&2`; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o
      check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `c1:num->real`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092PNRA_ROT1_TAC THEN
  SUBGOAL_THEN (parse_term (c1092ae_in "d1 d2 e1 e2 l" 4 "&87 / &50" "&2")) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [4] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL C1092MAR_DV C1092ANC_SUCCESSOR_FACES) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[c1092mar_successorFrame] o
    check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `c1:num->real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  C1092MPAPO_ORD_TAC THEN
  REWRITE_TAC[c1092pnrsup_input; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
              c1092psa_apart 4 5; c1092psa_apart 5 10] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC);;

(* Lean: actual_profile *)
let C1092PNRA_ACTUAL_PROFILE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> c1092pnrsup_profile cD sD (--vD - aD) uD aD"
    C1092AE_P C1092PNRA_IHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092PNRA_ACTUAL_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ C1092MAR_E @ c1092mabo_tr 10) C1092PNR_PROFILE) THEN
  ASM_REWRITE_TAC[c1092psa_unit 10; c1092psa_pos ()] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
  MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: actual_native *)
let C1092PNRA_ACTUAL_NATIVE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> &97 / &100 < cD /\\ &4 * --sD < cD /\\ vD + aD < &43 / &500"
    C1092AE_P C1092PNRA_IHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092PNRA_ACTUAL_PROFILE) THEN
  ASM_REWRITE_TAC[c1092pnrsup_profile] THEN STRIP_TAC THEN
  c1092mabo_normal_tac `cD:real` `--sD` THEN
  SUBGOAL_THEN `&0 < cD` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--sD < &1 / &4 * cD` ASSUME_TAC THENL
   [UNDISCH_TAC `--sD / cD < &1 / &4` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

let C1092PNRA_DPK3 = C1092MAR_DPK3;;

(* Lean: narrow_of_positive_predecessor *)
let C1092PNRA_NARROW_OF_POSITIVE_PREDECESSOR = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cW sW uW vW aW. %s /\\ %s /\\ c977cc_normal cC (--sC) /\\
      %s /\\ %s /\\ cW * cW + sW * sW = &1 /\\ &0 < aW /\\ c1092psa_frame d1 d2 e1 e2 l cW sW uW vW aW /\\
      c977cc_normal cW sW /\\ &0 < sW /\\ %s
      ==> &97 / &100 < cC /\\ &4 * --sC < cC /\\ vC + aC < &43 / &500"
    C1092AE_P C1092MPAPO_HYPS C1092MPOA_CHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092PNRA_DPK3
    (c1092mppe_in 5 "&2" "&3 / &2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `d10:num->real` (X_CHOOSE_THEN `d20:num->real` (X_CHOOSE_THEN `e10:num->real`
    (X_CHOOSE_THEN `e20:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d10:num->real`, list_mk_exists([`d20:num->real`; `e10:num->real`; `e20:num->real`],
       c1092mar_pk `EL 0 c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D0)))) THEN
  X_CHOOSE_THEN `d12:num->real` (X_CHOOSE_THEN `d22:num->real` (X_CHOOSE_THEN `e12:num->real`
    (X_CHOOSE_THEN `e22:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d12:num->real`, list_mk_exists([`d22:num->real`; `e12:num->real`; `e22:num->real`],
       c1092mar_pk `EL 1 c1092mpapo_rotation` C1092MAR_D C1092MAR_D2)))) THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D0 @ C1092MAR_CV) C1092MAR_IDENTITY_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ [`3`; `1`] @ C1092MAR_D0 @ C1092MAR_D @ C1092MAR_D2 @ C1092MAR_CV)
    C1092MAR_ROTATED_FRAME) THEN
  REWRITE_TAC[c1092mar_addSector] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092PNRA_DPK3)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,false,true)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 3 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 3 THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MANH_D5 @ C1092MAR_WV @ C1092MAR_D2 @ C1092MAR_CV) C1092PNRA_ACTUAL_NATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [5; 6] THEN ASM_REWRITE_TAC[]);;
