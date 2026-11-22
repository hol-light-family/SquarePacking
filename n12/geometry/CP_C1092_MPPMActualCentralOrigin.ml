(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualCentralOrigin.lean             *)
(* (N12Compact.C1092MPPMActualCentralOrigin; Lean header: "Source only,      *)
(* uncompiled").  NEGATIVE-FORWARD-POSITIVE-H Theorem 1.  Conventions of     *)
(* CP_C1092_MPPMActualRetaining.ml (ActualFrame c1092psa_frame,              *)
(* SuccessorFrame c1092mar_successorFrame, rotations EL i c1092mpapo_rotation,*)
(* clockwise C = (cC, sC, --vC - aC, uC, aC)); PositiveSource                 *)
(* c1092mabo_positiveSource.  Squares C, E are 5-tuples with their OpenSquare *)
(* invariants as hypotheses; upper / lower ABT_upper / ABT_lower; Frame of    *)
(* MPPMOrdinaryNegativeHalfpoint c1092onh_frame; positive_axes               *)
(* C1092NPPT_POSITIVE_AXES; strict_bounds ABT_STRICT_BOUNDS; upper_pos_neg    *)
(* C1092TFSU_UPPER_POS_NEG; Scalars.canonical_bounds C1092PRS_CANONICAL_BOUNDS.*)
(* The Lean lets k, ell, A, B are the polynomials written out.  The private  *)
(* mark is oo_seed.  Tag C1092MACO_.                                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualRetaining.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;

let C1092MACO_CV = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092MACO_EV = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;
let C1092MACO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: local_exclusion *)
let C1092MACO_LOCAL_EXCLUSION = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ &0 < sC /\ c977cc_normal cE (--sE) /\
     --cC - sC / &2 <= uC /\ vC + aC <= sC /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\ linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> ~linside cE sE uE vE aE (&0) (--(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MAP_EVERY (fun (c, s) -> c1092mabo_normal_tac c s) [`cC:real`, `sC:real`; `cE:real`, `--sE`] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092PRS_CANONICAL_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MACO_CV @ C1092MACO_EV) C1092NPPT_POSITIVE_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092onh_frame] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* current *)
    MP_TAC(SPECL (C1092MACO_EV @ [`&0`; `--(&1)`; `cC:real`; `sC:real`]) ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    (* transverse *)
    MP_TAC(SPECL (C1092MACO_EV @ [`&0`; `--(&13 / &50)`; `sC:real`; `--cC`]) ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    (* recipient *)
    MP_TAC(SPECL (C1092MACO_CV @ [`cE:real`; `sE:real`; `cC * cE + sC * sE`; `--(--cC * sE + sC * cE)`])
      C1092TFSU_UPPER_POS_NEG) THEN
    C1092MACO_PROD `&0 <= (cC - sC) * cE` THEN
    C1092MACO_PROD `&0 <= sC * (cE + sE)` THEN
    SUBGOAL_THEN `&0 <= cC * cE + sC * sE` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    C1092MACO_PROD `&0 <= cC * --sE` THEN C1092MACO_PROD `&0 < sC * cE` THEN
    SUBGOAL_THEN `&0 < --cC * sE + sC * cE` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `(--cC * sE + sC * cE) * (vC + aC) <= (--cC * sE + sC * cE) * sC` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(cC * cE + sC * sE) * (--cC - sC / &2) <= (cC * cE + sC * sE) * uC` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    C1092MACO_PROD `&0 < (aC - &1) * ((cC * cE + sC * sE) + (--cC * sE + sC * cE))` THEN
    C1092MACO_PROD `&0 <= cC * sC` THEN
    C1092MACO_PROD `&0 <= (cC + sC - &1) * (&17 / &7 - (&1 + cC + sC))` THEN
    SUBGOAL_THEN `&0 <= cC + sC - &1 - cC * sC / &2` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    C1092MACO_PROD `&0 <= cC * (&1 - cC)` THEN
    SUBGOAL_THEN `&0 < (cC + sC - &1 - cC * sC / &2) + (cC - sC + sC pow 2 / &2 - &13 / &50)` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
      NLIN_TAC [SQ_NONNEG `cC - sC`]; ALL_TAC] THEN
    C1092MACO_PROD `&0 <= (cC + sC - &1 - cC * sC / &2) * (cE + sE)` THEN
    C1092MACO_PROD `&0 <= ((cC + sC - &1 - cC * sC / &2) + (cC - sC + sC pow 2 / &2 - &13 / &50)) * --sE` THEN
    SUBGOAL_THEN `cE * (cC * cC + sC * sC) = cE` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
    UNDISCH_TAC `linside cE sE uE vE aE (&0) (--(&13 / &50))` THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
    POP_ASSUM_LIST(fun ths -> MP_TAC(end_itlist CONJ (filter (fun th ->
      let c = concl th in (is_binop `(<):real->real->bool` c || is_binop `(<=):real->real->bool` c || is_eq c) &&
        not (is_eq c && is_comb (lhs c) && fst (strip_comb (lhs c)) = `ABT_lower`)) ths))) THEN
    REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_ARITH]);;

(* Lean: mark (private) *)
let C1092MACO_MARK = C1092MPAPO_MARK;;

(* Lean: successor_retaining_excluded *)
let C1092MACO_SUCCESSOR_RETAINING_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s cE sE uE vE aE. %s /\\ cE * cE + sE * sE = &1 /\\ &0 < aE /\\
      c1092mar_successorFrame %s cE sE uE vE aE /\\ c977cc_normal cE (--sE) /\\ %s ==> ~%s"
    C1092AE_P C1092MPAPO_HYPS C1092AE_P (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 5 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term C1092MABO_MISSING9) ASSUME_TAC THENL
   [c1092mano_excl_tac 9 5 `&2` `&1`; ALL_TAC] THEN
  MP_TAC(SPECL C1092MAR_V C1092MABO_POSITIVE_SOURCE) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) C1092MACO_CV THEN
  REWRITE_TAC[c1092mabo_positiveSource] THEN STRIP_TAC THEN
  C1092MPAPO_ORD_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092mpapo_head `c1092psa_frame`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092mpapo_head `c1092psa_frame`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mar_successorFrame] o check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aE:real = l`))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `l:real`] C1092MACO_LOCAL_EXCLUSION) THEN
  ASM_REWRITE_TAC[ldisj] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
              c1092psa_apart 4 5] THEN
  ASM_REWRITE_TAC[]);;

let C1092MACO_DPK3 = C1092MAR_DPK3;;

(* Lean: nonpositive_retaining_excluded *)
let C1092MACO_NONPOSITIVE_RETAINING_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ %s ==> ~%s"
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
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_D2 @ C1092MACO_CV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MANH_D5 @ [`cC:real`; `sC:real`; `--vC - aC`; `uC:real`; `aC:real`])
    C1092MACO_SUCCESSOR_RETAINING_EXCLUDED) THEN
  ASM_REWRITE_TAC[] THEN
  c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [5] THEN ASM_REWRITE_TAC[]);;

(* Lean: retaining_excluded *)
let C1092MACO_RETAINING_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ &0 < cC /\\ abs sC <= cC /\\ %s ==> ~%s"
    C1092AE_P C1092MPAPO_HYPS C1092MPOA_CHYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 < sC` THENL
   [MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MACO_CV) C1092MABO_POSITIVE_PREVIOUS_EXCLUDED);
    MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MACO_CV) C1092MACO_NONPOSITIVE_RETAINING_EXCLUDED)] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;
