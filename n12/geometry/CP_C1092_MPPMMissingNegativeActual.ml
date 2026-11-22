(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeActual.lean           *)
(* (N12Compact.C1092MPPMMissingNegativeProfile; Lean header: "Source only,   *)
(* uncompiled").  Literal original weak and strong missing-negative profile  *)
(* adapters.  Conventions of CP_C1092_MPPMActualPositiveOrder.ml (Ordinary p *)
(* c1092mpapo_ordinary, ActualFrame p C c1092psa_frame with C's OpenSquare   *)
(* invariants as hypotheses).  Core / WeakFaces / StrongFaces / weak_profile *)
(* / strong_profile: c1092mnpg_core / c1092mnpg_weak_faces /                 *)
(* c1092mnpg_strong_faces / C1092MNPG_WEAK_PROFILE / C1092MNPG_STRONG_PROFILE*)
(* ; missing_halfpoint C1092PSA_MISSING_HALFPOINT; bottom_bar                *)
(* C1092MPAPO_BOTTOM_BAR; UnitCircleChord.increasing CCUCC_INCREASING.  The  *)
(* private side_gt / mark are OO_SIDE / oo_seed.  Tag C1092MNA_.             *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMMissingNegativeProfile.ml";;
needs "n12/geometry/CP_C1092_MPPMActualCentralOrigin.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

(* Lean: side_gt (private) *)
let C1092MNA_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: mark (private) *)
let C1092MNA_MARK = C1092MPAPO_MARK;;

let C1092MNA_MISSING = c1092mppe_in 4 "&87 / &50" "&2";;

(* Lean: actual_core *)
let C1092MNA_ACTUAL_CORE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\ %s ==> c1092mnpg_core cC sC uC vC aC"
    C1092AE_P C1092MPAPO_HYPS C1092MNA_MISSING C1092MPOA_CHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  MP_TAC(SPECL C1092MAR_V C1092PSA_MISSING_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[c1092mnpg_core] THEN C1092MAR_CFRAME_TAC THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`);
              c1092psa_excl 4 0 (c1092psa_seed 0 (`&1`, `&1`))] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ [`&2 + x`]) C1092MPAPO_BOTTOM_BAR) THEN
  ANTS_TAC THENL
   [CONV_TAC C1092PSA_CODE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC C1092PSA_CODE_CONV THEN
  MP_TAC(SPECL [`&2 + x`; `&1`] (c1092psa_apart 4 9)) THEN ASM_REWRITE_TAC[]);;

(* Lean: actual_weak *)
let C1092MNA_ACTUAL_WEAK = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\ %s /\\ c977cc_normal cC (--sC)
      ==> c1092mnpg_weak_faces cC sC uC vC aC" C1092AE_P C1092MPAPO_HYPS C1092MNA_MISSING C1092MPOA_CHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MNA_ACTUAL_CORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MABO_SIDE_TAC THEN
  MATCH_MP_TAC (SPECL C1092MAR_CV C1092MNPG_WEAK_PROFILE) THEN ASM_REWRITE_TAC[] THEN
  C1092MAR_CFRAME_TAC THEN CONV_TAC C1092PSA_CODE_CONV THEN
  ACCEPT_TAC(c1092psa_excl 4 8 (c1092psa_seed 8 (`&457 / &500`, `&2`))));;

(* Lean: actual_strong *)
let C1092MNA_ACTUAL_STRONG = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\ ~%s /\\ %s /\\ c977cc_normal cC (--sC)
      ==> c1092mnpg_strong_faces cC sC uC vC aC"
    C1092AE_P C1092MPAPO_HYPS C1092MNA_MISSING (c1092mppe_in 4 "&1" "&2") C1092MPOA_CHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MNA_ACTUAL_CORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MABO_SIDE_TAC THEN
  MATCH_MP_TAC (SPECL C1092MAR_CV C1092MNPG_STRONG_PROFILE) THEN ASM_REWRITE_TAC[] THEN
  C1092MAR_CFRAME_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: StrongFaces.sine_lower *)
let C1092MNA_STRONGFACES_SINE_LOWER = prove
 (`forall cC sC uC vC aC. cC * cC + sC * sC = &1 /\ &0 < aC /\ &1 < aC /\ c977cc_normal cC (--sC) /\
     c1092mnpg_strong_faces cC sC uC vC aC ==> &252 / &373 <= --sC`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mnpg_strong_faces] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  c1092mabo_normal_tac `cC:real` `--sC` THEN
  MP_TAC(SPECL [`&275 / &373`; `&252 / &373`; `cC:real`; `--sC`; `&11 / &25`; `&1`] CCUCC_INCREASING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;
