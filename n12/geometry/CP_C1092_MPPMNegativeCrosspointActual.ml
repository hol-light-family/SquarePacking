(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointActual.lean        *)
(* (N12Compact.C1092MPPMNegativeCrosspointGeometry; Lean header: "Source     *)
(* only, uncompiled").  Literal OOOO adapter for retaining-negative          *)
(* crosspoint transfer.  Conventions of                                      *)
(* CP_C1092_MPPMSteepPositiveNegativeProfileActual.ml (hypotheses            *)
(* C1092SPNPA_HYPS, clockwise D = (cD, sD, --vD - aD, uD, aD)) and           *)
(* CP_C1092_MPPMSteepPositiveThreeSquareActual.ml ((owners p 9).translated 2 *)
(* 2 = c1092mabo_tr 9).  Input / one_mode_negative / NegativeMode /          *)
(* ModesNonnegative / impossible_of_modes: c1092ncgd_input /                 *)
(* C1092NCG_ONE_MODE_NEGATIVE / c1092ncg_negativeMode /                      *)
(* c1092ncg_modesNonnegative / C1092NCG_IMPOSSIBLE_OF_MODES; Quarter         *)
(* c1092mncs_quarter.  ScalarProof is c1092nca_scalarProof.  The OpenSquare  *)
(* invariants of the witness Q are added to the existential.  The private    *)
(* mark is oo_seed.  Tag C1092NCA_.                                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveNegativeProfileActual.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareActual.ml";;

(* Lean: mark (private) *)
let C1092NCA_MARK = C1092MPAPO_MARK;;

let C1092NCA_B = c1092mabo_tr 9;;
let C1092NCA_BS = String.concat " " (map (fun t -> "(" ^ string_of_term t ^ ")") C1092NCA_B);;

(* Lean: actual_input *)
let C1092NCA_ACTUAL_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> c1092ncgd_input cC sC uC vC aC cD sD (--vD - aD) uD aD %s"
    C1092AE_P C1092SPNPA_HYPS C1092NCA_BS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092SPNPA_ACTUAL_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MPAPO_ORD_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MAR_V C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `c1:num->real`)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[c1092mar_successorFrame] o
    check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  REWRITE_TAC[c1092ncgd_input; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 9 (`&2`, `&457 / &500`); c1092psa_apart 9 4; c1092psa_apart 9 5] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092psa_box 9))) THEN
  REAL_ARITH_TAC);;

(* Lean: actual_negative_mode *)
let C1092NCA_ACTUAL_NEGATIVE_MODE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> ?cQ sQ uQ vQ aQ. cQ * cQ + sQ * sQ = &1 /\\ &0 < aQ /\\ aQ = l /\\
            (!x y. linside cQ sQ uQ vQ aQ x y <=> %s) /\\ c1092mncs_quarter cQ sQ /\\
            c1092ncg_negativeMode cC sC cD (--sD) cQ sQ"
    C1092AE_P C1092SPNPA_HYPS (c1092mppe_in 9 "&2 + x" "&2 + y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092NCA_ACTUAL_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_CV @ C1092MAR_E @ C1092NCA_B) C1092NCG_ONE_MODE_NEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c1092psa_unit 9; c1092psa_pos ()]; ALL_TAC] THEN
  CONV_TAC C1092PSA_CODE_CONV THEN REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN SIMP_TAC[]);;

(* Lean: ScalarProof *)
let c1092nca_scalarProof = new_definition
 `c1092nca_scalarProof <=>
    forall c s d t. c977cc_normal c s ==> c977cc_normal d t ==> &3 / &5 <= s ==> &8 * t <= &3 * d ==>
              c1092ncg_modesNonnegative c s d t`;;

(* Lean: crosspoint_of_scalars *)
let C1092NCA_CROSSPOINT_OF_SCALARS = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD.
      c1092nca_scalarProof /\\ %s /\\ ~%s /\\ %s /\\ %s /\\ %s /\\
      c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD (--sD) /\\ %s ==> %s"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MAR_CHYPS C1092MAR_DPK1 C1092MAR_DSQ
    (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 4 "&3 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092NCA_ACTUAL_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[c1092ncgd_input] o check (c1092mpapo_head `c1092ncgd_input`)) THEN
  MP_TAC(SPECL (C1092MAR_CV @ C1092MAR_E) C1092SPNP_PROFILE) THEN ASM_REWRITE_TAC[c1092spnp_faces] THEN
  STRIP_TAC THEN
  c1092mabo_normal_tac `cD:real` `--sD` THEN
  UNDISCH_TAC `--sD / cD < &3 / &8` THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&7 / &10 <= c ==> &0 < c`] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ C1092MAR_E @ C1092NCA_B) C1092NCG_IMPOSSIBLE_OF_MODES) THEN
  ASM_REWRITE_TAC[c1092psa_unit 9; c1092psa_pos ()] THEN
  CONV_TAC C1092PSA_CODE_CONV THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092nca_scalarProof` THEN REWRITE_TAC[c1092nca_scalarProof; IMP_IMP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spnp_input] o check (c1092mpapo_head `c1092spnp_input`)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
