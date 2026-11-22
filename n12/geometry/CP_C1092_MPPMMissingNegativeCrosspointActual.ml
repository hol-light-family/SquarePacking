(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointActual.lean *)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointGeometry; Lean header:      *)
(* "Source only, uncompiled").  Actual-owner entrance for the positive-to-   *)
(* missing-negative crosspoint transfer.  Conventions of                     *)
(* CP_C1092_MPPMNegativeCrosspointActual.ml (ActualFrame c1092psa_frame,     *)
(* rotation 1 packing (d1,d2,e1,e2) with C1092MAR_DPK1, clockwise D = (cD,   *)
(* sD, --vD - aD, uD, aD), (owners p 9).translated 2 2 = c1092mabo_tr 9).    *)
(* Input / RecipientInput / recipient_faces: c1092mncd_input /               *)
(* c1092mncf_recipientInput / C1092MNCF_RECIPIENT_FACES; one_mode_negative / *)
(* NegativeMode / ModesNonnegative / impossible_of_modes: C1092MNCGE_*;      *)
(* missing_profile C1092PSA_MISSING_PROFILE (c1092mmpf_faces);               *)
(* actual_missing_crosspoint_caps / steep_sine C1092MABO_*; southeast_of_    *)
(* missing C1092MANH_SOUTHEAST_OF_MISSING.  The OpenSquare invariants of the *)
(* witness Q are added to the existential.  The private side_gt / side_same  *)
(* / mark are OO_SIDE / l = l / oo_seed.  ScalarProof is                     *)
(* c1092mncac_scalarProof.  Tag C1092MNCAC_.                                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMActualRetaining.ml";;

(* Lean: side_gt (private) *)
let C1092MNCAC_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: side_same (private) *)
let C1092MNCAC_SIDE_SAME = C1092MPAPO_SIDE_SAME;;
(* Lean: mark (private) *)
let C1092MNCAC_MARK = C1092MPAPO_MARK;;

let c1092mncac_frame_of v th =
  c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = v;;

let C1092MNCAC_B = c1092mabo_tr 9;;
let C1092MNCAC_BS = String.concat " " (map (fun t -> "(" ^ string_of_term t ^ ")") C1092MNCAC_B);;

(* Lean: right_bar *)
let C1092MNCAC_RIGHT_BAR = prove
 (parse_term (Printf.sprintf "!%s y. %s /\\ --(&14 / &25) <= y /\\ y <= --(&13 / &50) ==> %s"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 10 "&3" "&2 + y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  c1092mpapo_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&87 / &50`] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

let C1092MNCAC_HYPS = Printf.sprintf "%s /\\ ~%s /\\ ~%s /\\ %s /\\ %s /\\ %s /\\
      c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD (--sD) /\\ ~%s"
  C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&3 / &2" "&2") C1092MAR_CHYPS
  C1092MAR_DPK1 C1092MAR_DSQ (c1092mppe_in 5 "&2" "&87 / &50");;

(* Lean: actual_input *)
let C1092MNCAC_ACTUAL_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> c1092mncd_input cC sC uC vC aC cD sD (--vD - aD) uD aD %s"
    C1092AE_P C1092MNCAC_HYPS C1092MNCAC_BS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092PSA_MISSING_PROFILE) THEN
  ASM_REWRITE_TAC[c1092mmpf_faces] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_ACTUAL_MISSING_CROSSPOINT_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092MABO_STEEP_SINE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MAR_V C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MAR_V C1092MANH_SOUTHEAST_OF_MISSING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "!y. --(&14 / &25) <= y ==> y <= --(&13 / &50) ==> ~%s"
      (c1092mppe_in 5 "&3" "&2 + y"))) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (parse_term (c1092mppe_in 10 "&3" "&2 + y")) ASSUME_TAC THENL
     [MATCH_MP_TAC (SPECL (C1092MAR_V @ [`y:real`]) C1092MNCAC_RIGHT_BAR) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL (C1092MAR_V @ [`5`; `10`]) C1092WC_OWNERS_DISJOINT) THEN
    ASM_REWRITE_TAC[ldisj; ARITH] THEN DISCH_THEN(MP_TAC o SPECL [`&3`; `&2 + y`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092mncac_frame_of `c1:num->real`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[c1092mar_successorFrame] o
    check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092mncac_frame_of `c1:num->real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092mncac_frame_of `d1:num->real`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  REWRITE_TAC[c1092mncd_input; c1092mncf_recipientInput; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
              c1092psa_seed 9 (`&2`, `&457 / &500`);
              c1092psa_excl 5 1 (c1092psa_seed 1 (`&3`, `&1`));
              c1092psa_apart 9 4; c1092psa_apart 9 5] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092psa_box 9))) THEN
  REAL_ARITH_TAC);;

(* Lean: actual_negative_mode *)
let C1092MNCAC_ACTUAL_NEGATIVE_MODE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> ?cQ sQ uQ vQ aQ. cQ * cQ + sQ * sQ = &1 /\\ &0 < aQ /\\ aQ = l /\\
            (!x y. linside cQ sQ uQ vQ aQ x y <=> %s) /\\ c1092mncs_quarter cQ sQ /\\
            c1092mncge_negativeMode cC sC cD (--sD) cQ sQ"
    C1092AE_P C1092MNCAC_HYPS (c1092mppe_in 9 "&2 + x" "&2 + y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092MNCAC_ACTUAL_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_CV @ C1092MAR_E @ C1092MNCAC_B) C1092MNCGE_ONE_MODE_NEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c1092psa_unit 9; c1092psa_pos ()]; ALL_TAC] THEN
  CONV_TAC C1092PSA_CODE_CONV THEN REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN SIMP_TAC[]);;

(* Lean: ScalarProof *)
let c1092mncac_scalarProof = new_definition
 `c1092mncac_scalarProof <=>
    forall c s d t. c977cc_normal c s ==> c977cc_normal d t ==> &3 / &5 <= s ==> &252 / &373 <= t ==>
              c1092mncge_modesNonnegative c s d t`;;

(* Lean: crosspoint_of_scalars *)
let C1092MNCAC_CROSSPOINT_OF_SCALARS = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD.
      c1092mncac_scalarProof /\\ %s /\\ ~%s /\\ %s /\\ %s /\\ %s /\\
      c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD (--sD) /\\ ~%s ==> %s"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MAR_CHYPS C1092MAR_DPK1 C1092MAR_DSQ
    (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 4 "&3 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092MNCAC_ACTUAL_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mncd_input] o check (c1092mpapo_head `c1092mncd_input`)) THEN
  MP_TAC(SPECL (C1092MAR_E @ C1092MNCAC_B) C1092MNCF_RECIPIENT_FACES) THEN
  ASM_REWRITE_TAC[c1092mncf_recipientFaces; c1092psa_unit 9; c1092psa_pos ()] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ C1092MAR_E @ C1092MNCAC_B) C1092MNCGE_IMPOSSIBLE_OF_MODES) THEN
  ASM_REWRITE_TAC[c1092psa_unit 9; c1092psa_pos ()] THEN
  UNDISCH_TAC `c1092mncac_scalarProof` THEN REWRITE_TAC[c1092mncac_scalarProof; IMP_IMP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
