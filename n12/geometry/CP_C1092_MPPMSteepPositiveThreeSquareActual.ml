(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMSteepPositiveThreeSquareActual.lean  *)
(* (N12Compact.C1092MPPMSteepPositiveThreeSquare; Lean header: "Source       *)
(* only").  Literal OOOO ledger in STEEP-POSITIVE-THREE-SQUARE-REDUCTION §5. *)
(* Conventions of CP_C1092_MPPMActualRetaining.ml (ActualFrame c1092psa_frame*)
(* , rotation 1 packing (d1,d2,e1,e2), clockwise D = (cD, sD, --vD - aD, uD, *)
(* aD), SuccessorFrame c1092mar_successorFrame); (owners p 9).translated 2 2 *)
(* is the tuple of C1092PSA_INSIDE_TRANSLATED (c1092mabo_tr 9).  Input /     *)
(* one_mode_negative: c1092spts_input / C1092SPTG_ONE_MODE_NEGATIVE;         *)
(* SuccessorFarCap Input / upper_cap: c1092spfc_input / C1092SPFC_UPPER_CAP; *)
(* Quarter, G00..G11: c1092mcs_quarter, c1092mcs_G00 ..; vertical_segment    *)
(* OO_VERTICAL_SEGMENT.  The OpenSquare invariants of the witness Q are      *)
(* added to the existential.  The private side_gt / side_same / mark are     *)
(* OO_SIDE / l = l / oo_seed.  Tag C1092SPTSA_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMActualRetaining.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveSuccessorFarCap.ml";;

(* Lean: side_gt (private) *)
let C1092SPTSA_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: side_same (private) *)
let C1092SPTSA_SIDE_SAME = C1092MPAPO_SIDE_SAME;;
(* Lean: mark (private) *)
let C1092SPTSA_MARK = C1092MPAPO_MARK;;

(* Lean: right_bar *)
let C1092SPTSA_RIGHT_BAR = prove
 (parse_term (Printf.sprintf "!%s y. %s /\\ --(&14 / &25) <= y /\\ y <= --(&2 / &5) ==> %s"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 10 "&3" "&2 + y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MAR_V C1092MPAWR_WALL_PAIRS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&8 / &5`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let C1092SPTSA_HYPS = Printf.sprintf "%s /\\ ~%s /\\ ~%s /\\ %s /\\ %s /\\ %s /\\
      c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD sD /\\ &0 < sD /\\ %s"
  C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&3 / &2" "&2") C1092MAR_CHYPS
  C1092MAR_DPK1 C1092MAR_DSQ (c1092mppe_in 5 "&2" "&3 / &2");;
let C1092SPTSA_B = c1092mabo_tr 9;;

(* Lean: actual_input *)
let C1092SPTSA_ACTUAL_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> c1092spts_input cC sC uC vC aC cD sD (--vD - aD) uD aD %s"
    C1092AE_P C1092SPTSA_HYPS (String.concat " " (map (fun t -> "(" ^ string_of_term t ^ ")") C1092SPTSA_B))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092PSA_MISSING_PROFILE) THEN ASM_REWRITE_TAC[c1092mmpf_faces] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_ACTUAL_MISSING_CROSSPOINT_CAPS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092MABO_STEEP_SINE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MAR_V C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the recipient faces in the rotated packing *)
  FIRST_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK1)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,true,false)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 1 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 1 THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MABO_POSITIVE_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mabo_normal_tac `cC:real` `sC:real` THEN
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
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[c1092mar_successorFrame] o
    check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  (* the far cap of the recipient *)
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`;
                `cD:real`; `sD:real`; `--vD - l`; `uD:real`; `l:real`] C1092SPFC_UPPER_CAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[c1092spfc_input; ldisj] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
    REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
                c1092psa_apart 4 5] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL (C1092MAR_V @ [`y:real`]) C1092SPTSA_RIGHT_BAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC C1092PSA_CODE_CONV THEN
    MP_TAC(SPECL [`&3`; `&2 + y`] (c1092psa_apart 5 10)) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[c1092spts_input; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 9 (`&2`, `&457 / &500`);
              c1092psa_apart 9 4; c1092psa_apart 9 5] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092psa_box 9))) THEN
  REAL_ARITH_TAC);;

(* Lean: actual_negative_mode *)
let C1092SPTSA_ACTUAL_NEGATIVE_MODE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> ?cQ sQ uQ vQ aQ. cQ * cQ + sQ * sQ = &1 /\\ &0 < aQ /\\ aQ = l /\\
            (!x y. linside cQ sQ uQ vQ aQ x y <=> %s) /\\ c1092mcs_quarter cQ sQ /\\
            (c1092mcs_G00 cC sC cD sD cQ sQ < &0 \\/ c1092mcs_G01 cC sC cD sD cQ sQ < &0 \\/
             c1092mcs_G10 cC sC cD sD cQ sQ < &0 \\/ c1092mcs_G11 cC sC cD sD cQ sQ < &0)"
    C1092AE_P C1092SPTSA_HYPS (c1092mppe_in 9 "&2 + x" "&2 + y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092SPTSA_ACTUAL_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_CV @ C1092MAR_E @ C1092SPTSA_B) C1092SPTG_ONE_MODE_NEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c1092psa_unit 9; c1092psa_pos ()]; ALL_TAC] THEN
  CONV_TAC C1092PSA_CODE_CONV THEN REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN SIMP_TAC[]);;
