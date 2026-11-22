(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveNegativeSupport.lean   *)
(* (N12Compact.C1092MPPMInwardPositive).  Three common support exclusions    *)
(* for the positive missing-center inward endings.  Squares C = cC sC uC vC *)
(* aC and E = cE sE uE vE aE (unit normals and positive sides explicit).     *)
(* PairInput: c1092ipsf_pair; Input/profile: c1092ipp_input/C1092IPP_PROFILE;*)
(* SuccessorFaces/successor_faces/successor_axes: c1092mane_successorFaces / *)
(* C1092MANE_SUCCESSOR_FACES / C1092MANE_SUCCESSOR_AXES; upper/lower:        *)
(* ABT_upper/ABT_lower; NegativeScalars.k/ell: c1092ipns_k/c1092ipns_ell.    *)
(* Tag C1092IPNSU_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveNegativeScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinaryElbow.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveSuccessorFaces.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/ABTransverse.ml";;

let c1092ipnsu_all vs t = list_mk_forall(vs, t);;

let C1092IPNSU_HYP =
  `cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
   c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE /\ c977cc_normal cE (--sE)`;;

(* unfold PairInput, Input, the Profile of C *)
let C1092IPNSU_SETUP_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipsf_pair] o
    check (fun th -> can (term_match [] `c1092ipsf_pair a b c d e f g h i j`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092minf_data] o
    check (fun th -> can (term_match [] `c1092minf_data a b c d e`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092IPP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092ipp_profile] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipp_input] o
    check (fun th -> can (term_match [] `c1092ipp_input a b c d e`) (concl th)));;

(* Lean: negative_faces *)
let C1092IPNSU_NEGATIVE_FACES = prove
 (c1092ipnsu_all [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
   (mk_imp(C1092IPNSU_HYP, `c1092mane_successorFaces cE sE uE vE aE`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092IPNSU_SETUP_TAC THEN
  MATCH_MP_TAC C1092MANE_SUCCESSOR_FACES THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aE` THEN REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `--(&1 / &2)`]) THEN ASM_REWRITE_TAC[]);;

(* the facts shared by the two support theorems *)
let C1092IPNSU_FACTS_TAC =
  C1092IPNSU_SETUP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092IPNSU_NEGATIVE_FACES) THEN
  ASM_REWRITE_TAC[c1092mane_successorFaces] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092IPNS_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  SUBGOAL_THEN `&0 < (aC - &1) * (&1 + c1092ipns_k cC sC cE (--sE) + c1092ipns_ell cC sC cE (--sE))`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC];;

let C1092IPNSU_K = `c1092ipns_k cC sC cE (--sE)`;;
let C1092IPNSU_L = `c1092ipns_ell cC sC cE (--sE)`;;

(* 0 <= w /\ a <= b ==> w * a <= w * b, as an assumption *)
let C1092IPNSU_MUL_TAC w ineq =
  let th = ASSUME ineq in
  MP_TAC(MATCH_MP REAL_LE_LMUL (CONJ (ASSUME (mk_binop `(<=):real->real->bool` `&0` w)) th)) THEN
  DISCH_TAC;;

let C1092IPNSU_DEF_TAC =
  REWRITE_TAC[c1092ipns_k; c1092ipns_ell] THEN REAL_ARITH_TAC;;

(* Lean: target_support_of_cap *)
let C1092IPNSU_TARGET_SUPPORT_OF_CAP = prove
 (c1092ipnsu_all [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `H:real`]
   (mk_imp(mk_conj(C1092IPNSU_HYP,
     `vC + aC <= H /\
      &0 < &1 - cE + sE + c1092ipns_k cC sC cE (--sE) * (&1 - cC - (&2 / &5) * sC) +
           c1092ipns_ell cC sC cE (--sE) * (&1 - H)`),
     `uE < ABT_upper cC sC uC vC aC cE sE`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092IPNSU_FACTS_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`;
                C1092IPNSU_K; mk_comb(`(--):real->real`, C1092IPNSU_L)] C1092TFSU_UPPER_POS_NEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY C1092IPNSU_DEF_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092ipns_k cC sC cE (--sE) /\ &0 <= c1092ipns_ell cC sC cE (--sE)`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092IPNSU_MUL_TAC C1092IPNSU_K `--cC - (&2 / &5) * sC <= uC` THEN
  C1092IPNSU_MUL_TAC C1092IPNSU_L `vC + aC <= H` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      let t = concl th in is_binary "real_lt" t || is_binary "real_le" t)) THEN
  REWRITE_TAC[c1092ipns_k; c1092ipns_ell] THEN REAL_ARITH_TAC);;

(* Lean: impossible_of_target *)
let C1092IPNSU_IMPOSSIBLE_OF_TARGET = prove
 (c1092ipnsu_all [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
   (mk_imp(mk_conj(C1092IPNSU_HYP, `uE < ABT_upper cC sC uC vC aC cE sE`), `false`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092IPNSU_FACTS_TAC THEN
  SUBGOAL_THEN `&0 <= c1092ipns_k cC sC cE (--sE) /\ &0 <= c1092ipns_ell cC sC cE (--sE)`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  SUBGOAL_THEN `uE <= cE - sE - aC /\ vE <= --sE - (&2 / &5) * cE - aC /\
                aC - cC - (&2 / &5) * sC <= uC + aC /\ aC + (&2 / &5) * sC - cC <= vC + aC`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092MANE_SUCCESSOR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  let finish =
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      let t = concl th in is_binary "real_lt" t || is_binary "real_le" t)) THEN
    REWRITE_TAC[c1092ipns_k; c1092ipns_ell] THEN REAL_ARITH_TAC in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [(* current *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                  C1092IPNSU_K; C1092IPNSU_L] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IPNSU_DEF_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
      can (find_term (fun t -> t = `ABT_lower cE sE uE vE aC cC sC`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092IPNSU_MUL_TAC C1092IPNSU_K `uE <= cE - sE - aC` THEN
    C1092IPNSU_MUL_TAC C1092IPNSU_L `vE <= --sE - (&2 / &5) * cE - aC` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092MANS_SOURCE_LONGITUDINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN finish;
    (* downward *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`; `--cC`;
                  C1092IPNSU_L; mk_comb(`(--):real->real`, C1092IPNSU_K)] C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY C1092IPNSU_DEF_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN `ABT_upper cC sC uC vC aC sC (--cC) = --vC` ASSUME_TAC THENL
     [REWRITE_TAC[REWRITE_RULE[REAL_NEG_NEG] (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
        `--sC`; `cC:real`] C1092TFSU_UPPER_NEG)] THEN
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
      can (find_term (fun t -> t = `ABT_lower cE sE uE vE aC sC (--cC)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092IPNSU_MUL_TAC C1092IPNSU_L `uE <= cE - sE - aC` THEN
    C1092IPNSU_MUL_TAC C1092IPNSU_K `--(&543 / &500) * cE <= vE` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092IPNS_DOWNWARD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN finish;
    (* own *)
    finish;
    (* transverse *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sE`; `cE:real`;
                  C1092IPNSU_L; C1092IPNSU_K] C1092TFSU_UPPER_POS_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IPNSU_DEF_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
      can (find_term (fun t -> t = `ABT_upper cC sC uC vC aC (--sE) cE`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092IPNSU_MUL_TAC C1092IPNSU_L `aC - cC - (&2 / &5) * sC <= uC + aC` THEN
    C1092IPNSU_MUL_TAC C1092IPNSU_K `aC + (&2 / &5) * sC - cC <= vC + aC` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092IPNS_TRANSVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN finish]);;
