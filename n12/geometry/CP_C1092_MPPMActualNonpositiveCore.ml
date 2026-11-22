(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualNonpositiveCore.lean           *)
(* (N12Compact.C1092MPPMActualNonpositive; Lean header: "Source only,        *)
(* uncompiled").  Shared literal actual entrance for the nonpositive         *)
(* ordinary comparisons.  Conventions of CP_C1092_MPPMActualCentralOrigin.ml *)
(* (ActualFrame c1092psa_frame with C's OpenSquare invariants as hypotheses, *)
(* hypotheses C1092NFA_NHYPS); C.translated (-2) (-2) / owner_frame:          *)
(* C1092MPOA_CT / C1092MPOA_OWNER_FRAME; ActualNegativeHalfpoint.southwest   *)
(* C1092MANH_SOUTHWEST; bottom_origin_of_halfpoint                           *)
(* C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT; NegativeForwardActual.bottom_segment *)
(* C1092NFA_BOTTOM_SEGMENT; AllNonpositive.Core c1092anc_core;               *)
(* ActualCentralOrigin.previous_excluded C1092MACOM_PREVIOUS_EXCLUDED.        *)
(* The private marker_point is C1092PSA_MARKER_POINT / oo_seed.              *)
(* Tag C1092MANC_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositiveCore.ml";;
needs "n12/geometry/CP_C1092_MPPMActualCentralOriginMissing.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeForwardActual.ml";;

(* Lean: halfpoint *)
let C1092MANC_HALFPOINT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> %s"
    C1092AE_P C1092NFA_NHYPS (c1092mppe_in 4 "&1" "&3 / &2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mabo_normal_tac `cC:real` `--sC` THEN
  MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MPOA_CT) C1092MANH_SOUTHWEST) THEN
  ASM_SIMP_TAC[C1092MPOA_OWNER_FRAME] THEN ASM_REAL_ARITH_TAC);;

(* Lean: bottom_origin *)
let C1092MANC_BOTTOM_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> %s"
    C1092AE_P C1092NFA_NHYPS (c1092mppe_in 9 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MACO_CV) C1092MANC_HALFPOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL C1092MAR_V C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT) THEN ASM_REWRITE_TAC[]);;

(* Lean: bottom_bar *)
let C1092MANC_BOTTOM_BAR = C1092NFA_BOTTOM_SEGMENT;;

(* Lean: marker_point (private) *)
let C1092MANC_MARKER_POINT = C1092PSA_MARKER_POINT;;

(* Lean: actual_core *)
let C1092MANC_ACTUAL_CORE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s ==> c1092anc_core cC sC uC vC aC"
    C1092AE_P C1092NFA_NHYPS (c1092mppe_in 4 "&87 / &50" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MACO_CV) C1092MANC_HALFPOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MACO_CV) C1092MACOM_PREVIOUS_EXCLUDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal cC (--sC)` THEN
    REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  C1092MPAPO_ORD_TAC THEN C1092MABO_SIDE_TAC THEN
  REWRITE_TAC[c1092anc_core] THEN ASM_REWRITE_TAC[] THEN C1092MAR_CFRAME_TAC THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`);
              c1092psa_excl 4 0 (c1092psa_seed 0 (`&1`, `&1`));
              c1092psa_excl 4 7 (c1092psa_seed 7 (`&33 / &20`, `&47 / &20`))] THEN
  ASM_REWRITE_TAC[]);;
