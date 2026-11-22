(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveMissingLeftCenter.lean       *)
(* (N12Compact.C1092MPPMPositiveMissingLeftCenter; Lean header: "Source      *)
(* only").  The full-angle scalar and the literal actual left-center         *)
(* consequence of POSITIVE-MISSING-LEFT-CENTER.  Conventions of              *)
(* CP_C1092_MPPMMissingNegativeCentersActual.ml (ActualFrame c1092psa_frame, *)
(* rotation 1 packing (d1,d2,e1,e2) with C1092MAR_DPK1; (owners p 8)         *)
(* .translated 2 2 is c1092mabo_tr 8, center_translate C1092MNCA_TR_CENTER). *)
(* ell is c1092scs_ell; missing_data C1092MPAPO_MISSING_DATA; Missing-       *)
(* PositiveBoundaries.profile / left_order C1092MPBP_PROFILE /               *)
(* C1092MPBE_LEFT_ORDER; MissingNegativeCenters.actual_bottom_order          *)
(* C1092MNCA_ACTUAL_BOTTOM_ORDER; bottom_origin_of_missing                   *)
(* C1092PSA_BOTTOM_ORIGIN_OF_MISSING.  scalar_positive is proved directly on *)
(* the whole quarter arc (ARC_NONNEG) instead of the half-angle substitution;*)
(* the private marker_point is oo_seed (c1092psa_seed).  Tag C1092PMLC_.     *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualBoundaryOrigin.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundEnvelopes.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryHalf.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCentersActual.ml";;

let C1092PMLC_ARC = ARC_NONNEG
  `&3 / &2 - (&6 / &5) * c - (&36 / &25) * s + s * (c + s) / &2 - &1 / &20`;;

(* Lean: scalar_positive *)
let C1092PMLC_SCALAR_POSITIVE = prove
 (`forall c s. c977cc_normal c s ==> &0 < &3 / &2 - (&6 / &5) * c - (&36 / &25) * s + s * (c + s) / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] (ASSUME `c977cc_normal c s`)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PMLC_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: center_threshold *)
let C1092PMLC_CENTER_THRESHOLD = prove
 (`forall cC sC (uC:real) vC aC Y.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ &1 < aC /\ c977cc_normal cC sC /\
     (&14 / &25) * sC - cC <= vC /\ c1092scs_ell aC cC sC (vC + aC) <= Y
     ==> &1 / &5 < Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092PMLC_SCALAR_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < cC` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cC * c1092scs_ell aC cC sC (vC + aC) =
                (vC + aC) - &2 * sC + (aC / &2) * (&1 + sC * (cC + sC))` ASSUME_TAC THENL
   [REWRITE_TAC[c1092scs_ell] THEN MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cC * c1092scs_ell aC cC sC (vC + aC) <= cC * Y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sC * (cC + sC)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (aC - &1) * (&3 / &2 + sC * (cC + sC) / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cC * (Y - &1 / &5)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `Y - &1 / &5`] (CONJUNCT1 REAL_LT_MUL_EQ)) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Lean: marker_point (private) *)
let C1092PMLC_MARKER_POINT = C1092PSA_MARKER_POINT;;

(* Lean: actual_left_center *)
let C1092PMLC_ACTUAL_LEFT_CENTER = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\ %s /\\ %s ==> &11 / &5 < lcy %s"
    C1092AE_P C1092MPAPO_HYPS (c1092mpapo_in 4 "&87 / &50" "&2") (c1092mpapo_in 8 "&1" "&2")
    C1092MPAPO_CHYPS (c1092ae_own C1092AE_P 8)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MACO_CV) C1092MPAPO_MISSING_DATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MABO_SIDE_TAC THEN
  MP_TAC(SPECL C1092MACO_CV C1092MPBP_PROFILE) THEN ASM_REWRITE_TAC[c1092mpbp_profile] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MACO_CV @ c1092mabo_tr 8) C1092MPBE_LEFT_ORDER) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092mpapo_head `c1092psa_frame`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[c1092psa_unit 8; c1092psa_pos (); ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
    REWRITE_TAC[c1092psa_seed 8 (`&457 / &500`, `&2`); c1092psa_apart 4 8] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092psa_box 8))) THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MACO_CV @ [list_mk_comb(`lcy`, c1092mabo_tr 8)]) C1092PMLC_CENTER_THRESHOLD) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092PSA_CODE_CONV THEN
  SIMP_TAC[MP (SPECL (fst (chop_list 4 (c1092psa_own 8)) @ [`l:real`]) C1092MNCA_TR_CENTER) (c1092psa_unit 8)] THEN
  REAL_ARITH_TAC);;
(* Lean: negative_missing_successor_missing_impossible *)
let C1092PMLC_NEGATIVE_MISSING_SUCCESSOR_MISSING_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s /\\ %s /\\ c977cc_normal cC (--sC) /\\
      %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD sD /\\
      ~%s /\\ ~%s ==> F"
    C1092AE_P C1092MPAPO_HYPS C1092MPOA_CHYPS C1092MAR_DPK1 C1092MAR_DSQ
    (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 5 "&2" "&87 / &50")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MACO_CV) C1092MNCA_ACTUAL_BOTTOM_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK1)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,true,false)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 1 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 1 THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092ae_in "d1 d2 e1 e2 l" 4 "&87 / &50" "&2"))) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [4] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (c1092mppe_in 9 "&2" "&1")) ASSUME_TAC THENL
   [c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN C1092MPAPO_ORD_TAC THEN
    MATCH_MP_TAC (SPECL C1092MAR_V C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (c1092ae_in "d1 d2 e1 e2 l" 8 "&1" "&2")) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [8] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092PMLC_ACTUAL_LEFT_CENTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL ([`(true,true,false)`] @ C1092MPAPO_V4 @ [`l:real`] @ C1092MAR_D @ [`8`]) C1092OT_OWNERS_TRANSPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; ALL_TAC] THEN
  REWRITE_TAC[c1092ae_act_conv `c1092ws_owner_action (true,true,false) 8`;
              c1092ot_pull; c1092ot_px; c1092ot_py; c1092ot_psw; I_THM; PAIR_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC (parse_term (Printf.sprintf "&9 / &5 < lcx %s" (c1092ae_own C1092AE_P 9))) THEN
  MP_TAC(SPECL (C1092MAR_V @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;
