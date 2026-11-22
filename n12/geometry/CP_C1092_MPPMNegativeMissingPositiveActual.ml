(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeMissingPositiveActual.lean   *)
(* (N12Compact.C1092MPPMNegativeMissingPositiveActual; Lean header: "Source  *)
(* only, uncompiled").  The original missing-negative to positive-retaining *)
(* edge.  Conventions of CP_C1092_MPPMNegativeOwnedPositiveActual.ml         *)
(* (ActualFrame c1092psa_frame; rotation packings with C1092MAR_DPK1/3; the  *)
(* triple clockwise turn W = (cD, sD, vD, --uD - aD, aD); (owners p 8)       *)
(* .translated 2 2 = c1092mabo_tr 8, center_translate C1092MNCA_TR_CENTER). *)
(* NegativeMissingPositiveCeiling Input / half_lt: c1092nmpcl_input /        *)
(* C1092NMPCL_HALF_LT; NegativeRecipientWall.Scalars.weak_bounds             *)
(* C1092NRWS_WEAK_BOUNDS; SharedWall Data / left_order / Scalars.bounds:     *)
(* c1092nmpsw_data / C1092NMPSW_LEFT_ORDER / C1092NMPS_BOUNDS;               *)
(* missing_strong_profile C1092MACOM_MISSING_STRONG_PROFILE                  *)
(* (c1092mnpg_strong_faces); forward_crosspoint C1092MAR_FORWARD_CROSSPOINT; *)
(* MissingNegativeCenters.actual_bottom_order C1092MNCA_ACTUAL_BOTTOM_ORDER. *)
(* The private mark is oo_seed.  Tag C1092NMPA_.                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMNegativeMissingPositiveCeiling.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeMissingPositiveSharedWall.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveMissingLeftCenter.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveActual.ml";;

(* Lean: mark (private) *)
let C1092NMPA_MARK = C1092MPAPO_MARK;;

let C1092NMPA_ROT3_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK3)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,false,true)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 3 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 3 THEN DISCH_TAC;;

let C1092NMPA_HYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\
      c977cc_normal cD (--sD) /\\ ~%s"
  C1092MABO_PHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MAR_DPK3 C1092MAR_DSQ (c1092mppe_in 7 "&2" "&113 / &50");;

(* Lean: positive_half_angle *)
let C1092NMPA_POSITIVE_HALF_ANGLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> sC / (&1 + cC) < &7 / &24" C1092AE_P C1092NMPA_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_POSITIVE_FACES) THEN
  ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092MPAPO_ORD_TAC THEN C1092NMPA_ROT3_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092ae_in "d1 d2 e1 e2 l" 4 "&87 / &50" "&2"))) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [4] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MACOM_MISSING_STRONG_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[c1092mnpg_strong_faces; c1092mnpg_faces] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cD:real`; `--sD`] C1092NRWS_WEAK_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  c1092mabo_normal_tac `cD:real` `--sD` THEN
  SUBGOAL_THEN `&23 / &50 < cD * --sD` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (cD + --sD - &139 / &100) * (cD + --sD + &139 / &100)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `cD * cD + sD * sD = &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "!x y. linside cD sD vD (--uD - aD) aD x y <=> %s"
      (c1092mppe_in 7 "&2 + x" "&2 + y"))) ASSUME_TAC THENL
   [REWRITE_TAC[C1092MABO_INSIDE_CLOCKWISE3] THEN
    FIRST_ASSUM(fun th -> if c1092nopa_frame_of `d1:num->real` th
      then REWRITE_TAC[CONJUNCT2 (REWRITE_RULE[c1092psa_frame] th)] else NO_TAC) THEN
    c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [4] THEN C1092MAR_POINT_EQ_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ [`cD:real`; `sD:real`; `vD:real`; `--uD - aD`; `aD:real`])
    C1092NMPCL_HALF_LT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  REWRITE_TAC[c1092nmpcl_input; ldisj] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 7 (`&33 / &20`, `&47 / &20`);
              c1092psa_apart 4 7] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC);;

(* Lean: positive_lowerV *)
let C1092NMPA_POSITIVE_LOWERV = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ sC / (&1 + cC) <= &3 / &10
      ==> (&14 / &25) * sC - cC <= vC" C1092AE_P C1092MPAPO_HYPS C1092MAR_CHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092NMPS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mabo_normal_tac `cC:real` `sC:real` THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\ linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
                linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
    REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`)] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (--(&14 / &25)) (--(&1))` MP_TAC THENL
   [MAP_EVERY (fun tm -> UNDISCH_TAC tm)
     [`linside cC sC uC vC aC (--(&1)) (--(&2 / &5))`; `linside cC sC uC vC aC (--(&1)) (--(&13 / &50))`;
      `linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20))`] THEN
    REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  c1092mpapo_excl_tac 4 9 `&36 / &25` `&1`);;

(* Lean: missing_predecessor_retaining_impossible *)
let C1092NMPA_MISSING_PREDECESSOR_RETAINING_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s ==> F"
    C1092AE_P C1092NMPA_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092NMPA_POSITIVE_HALF_ANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sC / (&1 + cC) <= &3 / &10` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_POSITIVE_FACES) THEN
  ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MAR_FORWARD_CROSSPOINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092NMPA_POSITIVE_LOWERV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092MPAPO_ORD_TAC THEN C1092NMPA_ROT3_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092ae_in "d1 d2 e1 e2 l" 4 "&87 / &50" "&2"))) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [4] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* leftOrigin *)
  SUBGOAL_THEN (parse_term (c1092mppe_in 8 "&1" "&2")) ASSUME_TAC THENL
   [MP_TAC(SPECL C1092MANH_D5 C1092MPAWR_BOTTOM_ORDINARY) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpapo_ordinary] o
      check (fun th -> c1092mpapo_head `c1092mpapo_ordinary` th &&
                       hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
    MP_TAC(SPECL C1092MANH_D5 C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN ASM_REWRITE_TAC[] THEN
    c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [9] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MACO_CV @ c1092mabo_tr 8) C1092NMPSW_LEFT_ORDER) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
    ASM_REWRITE_TAC[c1092psa_unit 8; c1092psa_pos (); c1092nmpsw_data; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
    REWRITE_TAC[c1092psa_seed 8 (`&457 / &500`, `&2`); c1092psa_apart 4 8] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092psa_box 8))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC C1092PSA_CODE_CONV THEN
  SIMP_TAC[MP (SPECL (fst (chop_list 4 (c1092psa_own 8)) @ [`l:real`]) C1092MNCA_TR_CENTER) (c1092psa_unit 8)] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MNCA_ACTUAL_BOTTOM_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL ([`(true,false,true)`] @ C1092MPAPO_V4 @ [`l:real`] @ C1092MAR_D @ [`9`]) C1092OT_OWNERS_TRANSPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; ALL_TAC] THEN
  REWRITE_TAC[c1092ae_act_conv `c1092ws_owner_action (true,false,true) 9`;
              c1092ot_pull; c1092ot_px; c1092ot_py; c1092ot_psw; I_THM; PAIR_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC (parse_term (Printf.sprintf "&1 / &5 < lcy %s - &2"
    (String.concat " " (map (fun t -> "(" ^ string_of_term t ^ ")") (c1092psa_own 8))))) THEN
  MP_TAC(SPECL (C1092MAR_V @ [`EL 8 c1092wc_code`]) OO_UNIT) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092PSA_CODE_CONV THEN
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

let C1092NMPA_D2PK3 = C1092NOPA_D2PK3;;

(* Lean: successor_retaining_impossible *)
let C1092NMPA_SUCCESSOR_RETAINING_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s /\\ %s /\\ c977cc_normal cC (--sC) /\\
      ~%s /\\ %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD sD /\\ &0 < sD /\\ %s
      ==> F"
    C1092AE_P C1092MPAPO_HYPS C1092MPOA_CHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MAR_DPK1 C1092MAR_DSQ
    (c1092mppe_in 5 "&2" "&87 / &50")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `d10:num->real` (X_CHOOSE_THEN `d20:num->real` (X_CHOOSE_THEN `e10:num->real`
    (X_CHOOSE_THEN `e20:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d10:num->real`, list_mk_exists([`d20:num->real`; `e10:num->real`; `e20:num->real`],
       c1092mar_pk `EL 0 c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D0)))) THEN
  X_CHOOSE_THEN `d12:num->real` (X_CHOOSE_THEN `d22:num->real` (X_CHOOSE_THEN `e12:num->real`
    (X_CHOOSE_THEN `e22:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d12:num->real`, list_mk_exists([`d22:num->real`; `e12:num->real`; `e22:num->real`],
       c1092mar_pk `EL 3 c1092mpapo_rotation` C1092MAR_D C1092MAR_D2)))) THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D0 @ C1092MAR_CV) C1092MAR_IDENTITY_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ [`1`; `3`] @ C1092MAR_D0 @ C1092MAR_D @ C1092MAR_D2 @ C1092MAR_CV)
    C1092MAR_ROTATED_FRAME) THEN
  REWRITE_TAC[c1092mar_addSector] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK1)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,true,false)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 1 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 1 THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MANH_D5 @ C1092MAR_DV @ C1092MAR_D2 @ C1092MAR_CV)
    C1092NMPA_MISSING_PREDECESSOR_RETAINING_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN
  c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [4; 7] THEN ASM_REWRITE_TAC[]);;
