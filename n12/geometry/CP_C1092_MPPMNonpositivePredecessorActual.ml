(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNonpositivePredecessorActual.lean    *)
(* (N12Compact.C1092MPPMAllNonpositive; Lean header: "Source only,           *)
(* uncompiled").  Literal missing-negative predecessor application of the   *)
(* narrow retaining profile.  Conventions of CP_C1092_MPPMActualRetaining.ml *)
(* and CP_C1092_MPPMNegativeOwnedPositiveActual.ml (ActualFrame              *)
(* c1092psa_frame; rotation 3 packing (d1,d2,e1,e2) with C1092MAR_DPK3;      *)
(* counterclockwise D = (cD, sD, vD, --uD - aD, aD)                          *)
(* (C1092MANP_INSIDE_COUNTERCLOCKWISE); (owners p 9).translated 2 2 is       *)
(* c1092nopa_tr).  missing_strong_profile C1092MACOM_MISSING_STRONG_PROFILE; *)
(* missing_predecessor C1092MANP_MISSING_PREDECESSOR; predecessor_shallow    *)
(* C1092ANSH_PREDECESSOR_SHALLOW; ActualNonpositive.actual_core / bottom_bar *)
(* C1092MANC_*.  The private marker_point is oo_seed.  Tag C1092NPPA_.       *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositiveShallow.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonpositiveCore.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveActual.ml";;

(* Lean: marker_point (private) *)
let C1092NPPA_MARKER_POINT = C1092PSA_MARKER_POINT;;

(* Lean: narrow_of_missing_predecessor *)
let C1092NPPA_NARROW_OF_MISSING_PREDECESSOR = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s /\\ %s /\\
      %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD (--sD) /\\ ~%s
      ==> c1092ansh_shallow cC sC uC vC aC"
    C1092AE_P C1092NFA_NHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MAR_DPK3 C1092MAR_DSQ
    (c1092mppe_in 7 "&2" "&113 / &50")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "!x. --(&14 / &25) <= x ==> x <= &0 ==> linside %s x (--(&1))"
      (c1092nopa_trs C1092MAR_V 9))) ASSUME_TAC THENL
   [REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV) C1092MANC_BOTTOM_BAR) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK3)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,false,true)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 3 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 3 THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092ae_in "d1 d2 e1 e2 l" 4 "&87 / &50" "&2"))) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [4] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MACOM_MISSING_STRONG_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&1 < aD` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL C1092MAR_DV C1092MANP_MISSING_PREDECESSOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the counterclockwise turn W of D is the original owner 7 *)
  SUBGOAL_THEN (parse_term (Printf.sprintf "!x y. linside cD sD vD (--uD - aD) aD x y <=> %s"
      (c1092mppe_in 7 "&2 + x" "&2 + y"))) ASSUME_TAC THENL
   [REWRITE_TAC[C1092MANP_INSIDE_COUNTERCLOCKWISE] THEN
    FIRST_ASSUM(fun th -> if c1092nopa_frame_of `d1:num->real` th
      then REWRITE_TAC[CONJUNCT2 (REWRITE_RULE[c1092psa_frame] th)] else NO_TAC) THEN
    c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [4] THEN C1092MAR_POINT_EQ_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ [`cD:real`; `sD:real`; `vD:real`; `--uD - aD`; `aD:real`] @
    c1092nopa_tr C1092MAR_V 9) C1092ANSH_PREDECESSOR_SHALLOW) THEN
  MP_TAC(SPECL (C1092MAR_V @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY RASM_ARITH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 7 (`&33 / &20`, `&47 / &20`); c1092psa_apart 4 7; c1092psa_apart 4 9]);;
