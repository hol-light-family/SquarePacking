(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualCentralOriginMissing.lean      *)
(* (N12Compact.C1092MPPMActualCentralOrigin; Lean header: "Source only").    *)
(* The universal preceding-origin exclusion.  Conventions of                 *)
(* CP_C1092_MPPMActualRetaining.ml / CP_C1092_MPPMActualCentralOrigin.ml     *)
(* (ActualFrame c1092psa_frame, (rotation i).pullPacking p is (d1,d2,e1,e2)  *)
(* with c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2),   *)
(* a pulled packing of a pulled packing uses d12 d22 e12 e22; clockwise      *)
(* (c,s,u,v,a) = (c, s, --v - a, u, a)); NegativeBoundary                    *)
(* c1092mabo_negativeBoundary; NegativeRecipientWall Input / steep:          *)
(* c1092nrw_input / C1092NRW_STEEP; Scalars.weak_bounds C1092NRWS_WEAK_BOUNDS;*)
(* MissingNegativeProfile actual_weak / actual_strong / StrongFaces:         *)
(* C1092MNA_ACTUAL_WEAK / C1092MNA_ACTUAL_STRONG / c1092mnpg_strong_faces.   *)
(* Squares are 5-tuples with their OpenSquare invariants as hypotheses.      *)
(* The private side_gt / side_same / marker_point are OO_SIDE / l = l /      *)
(* oo_seed.  Tag C1092MACOM_.                                                *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMNegativeRecipientWall.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeActual.ml";;

(* Lean: side_gt (private) *)
let C1092MACOM_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: side_same (private) *)
let C1092MACOM_SIDE_SAME = C1092MPAPO_SIDE_SAME;;
(* Lean: marker_point (private) *)
let C1092MACOM_MARKER_POINT = C1092PSA_MARKER_POINT;;

(* Lean: successor_missing_excluded *)
let C1092MACOM_SUCCESSOR_MISSING_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2 cD sD uD vD aD. %s /\\ %s /\\ %s /\\
      c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD (--sD) /\\ ~%s ==> ~%s"
    C1092AE_P C1092MPAPO_HYPS C1092MAR_DPK1 C1092MAR_DSQ
    (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 5 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term C1092MABO_MISSING9) ASSUME_TAC THENL
   [c1092mano_excl_tac 9 5 `&2` `&1`; ALL_TAC] THEN
  MP_TAC(SPECL C1092MAR_V C1092MABO_MISSING_BOTTOM_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) C1092MABO_BV THEN
  REWRITE_TAC[c1092mabo_negativeBoundary] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK1)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,true,false)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 1 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 1 THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092ae_in "d1 d2 e1 e2 l" 4 "&87 / &50" "&2"))) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [4] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MNA_ACTUAL_WEAK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mnpg_weak_faces; c1092mnpg_faces]) THEN
  MP_TAC(SPECL [`cD:real`; `--sD`] C1092NRWS_WEAK_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mar_successorFrame] o
    check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = l` || concl th = `aB:real = l`))) THEN
  MP_TAC(SPECL ([`cD:real`; `sD:real`; `--vD - l`; `uD:real`; `l:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`]) C1092NRW_STEEP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[c1092nrw_input; ldisj] THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) t)) (concl th)
      then REWRITE_TAC[th] else NO_TAC)) [`cB:real`; `--vD - l`] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
    (let wa = c1092psa_wa () in
     REWRITE_TAC[c1092psa_seed 9 (`&2`, `&457 / &500`); CONJUNCT1 (CONJUNCT2 wa); c1092psa_apart 9 5;
                 c1092psa_excl 9 0 (c1092psa_seed 0 (`&1`, `&457 / &500`))]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092psa_box 9))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  c1092mabo_normal_tac `cB:real` `--sB` THEN
  UNDISCH_TAC `--sB / cB < &1 / &4` THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&7 / &10 <= c ==> &0 < c`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: nonpositive_missing_excluded *)
let C1092MACOM_NONPOSITIVE_MISSING_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ ~%s ==> ~%s"
    C1092AE_P C1092MPAPO_HYPS C1092MPOA_CHYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `d1:num->real` (X_CHOOSE_THEN `d2:num->real` (X_CHOOSE_THEN `e1:num->real`
    (X_CHOOSE_THEN `e2:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d1:num->real`, list_mk_exists([`d2:num->real`; `e1:num->real`; `e2:num->real`],
       parse_term C1092MACO_DPK3)))) THEN
  X_CHOOSE_THEN `d10:num->real` (X_CHOOSE_THEN `d20:num->real` (X_CHOOSE_THEN `e10:num->real`
    (X_CHOOSE_THEN `e20:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d10:num->real`, list_mk_exists([`d20:num->real`; `e10:num->real`; `e20:num->real`],
       c1092mar_pk `EL 0 c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D0)))) THEN
  X_CHOOSE_THEN `d12:num->real` (X_CHOOSE_THEN `d22:num->real` (X_CHOOSE_THEN `e12:num->real`
    (X_CHOOSE_THEN `e22:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d12:num->real`, list_mk_exists([`d22:num->real`; `e12:num->real`; `e22:num->real`],
       c1092mar_pk `EL 1 c1092mpapo_rotation` C1092MAR_D C1092MAR_D2)))) THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D0 @ C1092MACO_CV) C1092MAR_IDENTITY_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ [`3`; `1`] @ C1092MAR_D0 @ C1092MAR_D @ C1092MAR_D2 @ C1092MACO_CV)
    C1092MAR_ROTATED_FRAME) THEN
  REWRITE_TAC[c1092mar_addSector] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MACO_DPK3)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,false,true)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 3 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 3 THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092ae_in "d1 d2 e1 e2 l" 5 "&2" "&87 / &50"))) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [5] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_D2 @ C1092MACO_CV) C1092MACOM_SUCCESSOR_MISSING_EXCLUDED) THEN
  ASM_REWRITE_TAC[] THEN
  c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [5] THEN ASM_REWRITE_TAC[]);;

(* Lean: previous_excluded *)
let C1092MACOM_PREVIOUS_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ abs sC <= cC ==> ~%s"
    C1092AE_P C1092MPAPO_HYPS C1092MPOA_CHYPS (c1092mppe_in 4 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 < sC` THENL
   [MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MACO_CV) C1092MABO_POSITIVE_PREVIOUS_EXCLUDED) THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cC (--sC)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 4 "&87 / &50" "&2")) THENL
   [MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MACO_CV) C1092MACO_NONPOSITIVE_RETAINING_EXCLUDED);
    MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MACO_CV) C1092MACOM_NONPOSITIVE_MISSING_EXCLUDED)] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: missing_strong_profile *)
let C1092MACOM_MISSING_STRONG_PROFILE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\ %s /\\ c977cc_normal cC (--sC)
      ==> c1092mnpg_strong_faces cC sC uC vC aC"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MPOA_CHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MACO_CV) C1092MACOM_PREVIOUS_EXCLUDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal cC (--sC)` THEN
    REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MACO_CV) C1092MNA_ACTUAL_STRONG) THEN
  ASM_REWRITE_TAC[]);;
