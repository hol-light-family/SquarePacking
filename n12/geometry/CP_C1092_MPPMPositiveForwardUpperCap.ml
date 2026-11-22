(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveForwardUpperCap.lean         *)
(* (N12Compact.C1092MPPMPositiveForwardUpperCap; Lean header: "Uncompiled"). *)
(* POSITIVE-FORWARD-UPPER-CAP on the original OOOO MPPM owners.  Conventions *)
(* of CP_C1092_MPPMPositiveOverlap.ml: owners p i at mask EL i c1092wc_code, *)
(* side l; Ordinary p is c1092mpapo_ordinary; ActualFrame p C is             *)
(* c1092psa_frame with C = cC sC uC vC aC and its OpenSquare invariants as   *)
(* hypotheses; Normal is c977cc_normal; ForwardCore / ForwardFaces are       *)
(* c1092pcs_forwardCore / c1092pcs_forwardFaces (forward_profile             *)
(* C1092PCS_FORWARD_PROFILE); forward_core C1092PSA_FORWARD_CORE;            *)
(* previous_absent / original_center_absent C1092MPOA_ names.               *)
(* Tag C1092MPFUC_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMPositiveOverlap.ml";;

let C1092MPFUC_V = C1092MPPE_V;;
let C1092MPFUC_CV = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092MPFUC_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;
let C1092MPFUC_NORMAL_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`));;

(* Lean: cap_of_backward_absent *)
let C1092MPFUC_CAP_OF_BACKWARD_ABSENT = prove
 (`forall cC sC uC vC aC.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ &1 < aC /\ c977cc_normal cC sC /\
     c1092pcs_forwardCore cC sC uC vC aC /\ ~linside cC sC uC vC aC (&0) (--(&13 / &50))
     ==> uC + aC <= --(&13 / &50) * sC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPFUC_NORMAL_TAC THEN
  MP_TAC(SPECL C1092MPFUC_CV C1092PCS_FORWARD_PROFILE) THEN ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `sC + (&13 / &50) * cC < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside cC sC uC vC aC (&0) (--(&13 / &50))` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c1092pcs_forwardCore] o
    check (fun th -> c1092mpapo_head `c1092pcs_forwardCore` th)) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN C1092MPFUC_LP_TAC);;

let C1092MPFUC_FORWARD = c1092mppe_in 4 "&87 / &50" "&2";;
let C1092MPFUC_HYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ c977cc_normal cC sC"
  C1092MPAPO_HYPS C1092MPFUC_FORWARD C1092MPOA_CHYPS;;

(* side, previous and core in the assumptions *)
let C1092MPFUC_CORE_TAC =
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092mpapo_head `c1092psa_frame`)) THEN
    MP_TAC(SPECL C1092MPFUC_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPFUC_V @ C1092MPFUC_CV) C1092MPOA_PREVIOUS_ABSENT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  C1092MPAPO_ORD_TAC THEN
  MP_TAC(SPECL (C1092MPFUC_V @ C1092MPFUC_CV) C1092PSA_FORWARD_CORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* Lean: upper_cap *)
let C1092MPFUC_UPPER_CAP = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ &0 < sC ==> uC + aC <= &0" C1092AE_P C1092MPFUC_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPFUC_CORE_TAC THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 4 "&2" "&87 / &50")) THENL
   [MP_TAC(SPECL (C1092MPFUC_V @ C1092MPFUC_CV) C1092MPOA_ORIGINAL_CENTER_ABSENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `linside cC sC uC vC aC (&0) (--(&13 / &50))` ASSUME_TAC THENL
     [C1092MPAPO_FRAME_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    C1092MPFUC_NORMAL_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `linside cC sC uC vC aC (&0) (&0)` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c1092pcs_forwardCore] o
        check (fun th -> c1092mpapo_head `c1092pcs_forwardCore` th)) THEN
      UNDISCH_TAC `linside cC sC uC vC aC (&0) (--(&13 / &50))` THEN
      REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN C1092MPFUC_LP_TAC;
      C1092MPAPO_FRAME_TAC THEN ASM_REWRITE_TAC[]];
    MP_TAC(SPECL C1092MPFUC_CV C1092MPFUC_CAP_OF_BACKWARD_ABSENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MPAPO_FRAME_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < sC` THEN REAL_ARITH_TAC]);;

(* Lean: faces *)
let C1092MPFUC_FACES = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ &0 < sC
      ==> c1092pcs_forwardFaces cC sC uC vC aC /\\ uC + aC <= &0" C1092AE_P C1092MPFUC_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [C1092MPFUC_CORE_TAC THEN MATCH_MP_TAC (SPECL C1092MPFUC_CV C1092PCS_FORWARD_PROFILE) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC (SPECL (C1092MPFUC_V @ C1092MPFUC_CV) C1092MPFUC_UPPER_CAP) THEN ASM_REWRITE_TAC[]]);;

(* Lean: sharp_upper_cap *)
let C1092MPFUC_SHARP_UPPER_CAP = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ ~%s /\\ %s /\\ c977cc_normal cC sC
      ==> uC + aC <= --(&13 / &50) * sC"
    C1092AE_P C1092MPAPO_HYPS C1092MPFUC_FORWARD (c1092mppe_in 4 "&2" "&87 / &50") C1092MPOA_CHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPFUC_CORE_TAC THEN
  MATCH_MP_TAC (SPECL C1092MPFUC_CV C1092MPFUC_CAP_OF_BACKWARD_ABSENT) THEN
  ASM_REWRITE_TAC[] THEN C1092MPAPO_FRAME_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: center_absent *)
let C1092MPFUC_CENTER_ABSENT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ &0 < sC ==> ~%s"
    C1092AE_P C1092MPFUC_HYPS (c1092mppe_in 4 "&2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPFUC_V @ C1092MPFUC_CV) C1092MPFUC_UPPER_CAP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (&0) (&0)` MP_TAC THENL
   [C1092MPAPO_FRAME_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[linside] THEN UNDISCH_TAC `uC + aC <= &0` THEN REAL_ARITH_TAC]);;
