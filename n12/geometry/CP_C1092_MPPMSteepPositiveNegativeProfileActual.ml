(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMSteepPositiveNegativeProfileActual.  *)
(* lean (N12Compact.C1092MPPMSteepPositiveNegativeProfile; Lean header:      *)
(* "Source only, uncompiled").  Literal Q4/Q5 adapter for the steep-positive/*)
(* negative-retaining profile.  Conventions of CP_C1092_MPPMActualRetaining.ml*)
(* : ActualFrame p C is c1092psa_frame; (rotation 1).pullPacking p is        *)
(* (d1,d2,e1,e2) with c1092ot_pk (EL 1 c1092mpapo_rotation) (c1,c2,a,b) =    *)
(* (d1,d2,e1,e2); clockwise D = (cD, sD, --vD - aD, uD, aD).  Input / Faces /*)
(* profile: c1092spnp_input / c1092spnp_faces / C1092SPNP_PROFILE.           *)
(* The private mark is oo_seed.  Tag C1092SPNPA_.                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMSteepPositiveNegativeProfile.ml";;
needs "n12/geometry/CP_C1092_MPPMActualRetaining.ml";;

(* Lean: mark (private) *)
let C1092SPNPA_MARK = C1092MPAPO_MARK;;

let C1092SPNPA_HYPS = Printf.sprintf "%s /\\ ~%s /\\ ~%s /\\ %s /\\ %s /\\ %s /\\
      c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD (--sD) /\\ %s"
  C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&3 / &2" "&2") C1092MAR_CHYPS
  C1092MAR_DPK1 C1092MAR_DSQ (c1092mppe_in 5 "&2" "&87 / &50");;

(* Lean: actual_input *)
let C1092SPNPA_ACTUAL_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> c1092spnp_input cC sC uC vC aC cD sD (--vD - aD) uD aD" C1092AE_P C1092SPNPA_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[c1092mar_successorFrame] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_POSITIVE_FACES) THEN ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_ACTUAL_MISSING_CROSSPOINT_CAPS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  C1092MPAPO_ORD_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MAR_V C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092MABO_STEEP_SINE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o
      check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `c1:num->real`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `c1:num->real`)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
  DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  REWRITE_TAC[c1092spnp_input; ldisj] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
    c1092psa_excl 5 9 (c1092mano_lasm 9 "&2" "&1");
    c1092psa_excl 5 1 (c1092psa_seed 1 (`&3`, `&1`));
    c1092psa_apart 4 5] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC);;

(* Lean: actual_profile *)
let C1092SPNPA_ACTUAL_PROFILE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> c1092spnp_faces cD sD (--vD - aD) uD aD" C1092AE_P C1092SPNPA_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ C1092MAR_E) C1092SPNP_PROFILE) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092SPNPA_ACTUAL_INPUT) THEN
  ASM_REWRITE_TAC[]);;
