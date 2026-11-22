(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMSteepPositiveNegativeProfile.lean    *)
(* (namespace N12Compact.C1092MPPMSteepPositiveNegativeProfile).  Full       *)
(* actual-square STEEP-POSITIVE-NEGATIVE-PROFILE Theorem 1.  Squares         *)
(* C = (cC, ..), E = (cE, ..).  Input / Faces: c1092spnp_input /             *)
(* c1092spnp_faces; Scalars: C1092SNP_*, c1092snp_*; lower_nn / lower_pn:    *)
(* C1092WS_LOWER_NN / _PN; upper_pos_neg: C1092TFSU_UPPER_POS_NEG;           *)
(* relative / positive_axes: C1092NPP_RELATIVE / C1092NPPT_POSITIVE_AXES.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveNegativeProfileScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessor.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

(* Lean: Input (structure) *)
let c1092spnp_input = new_definition
 `c1092spnp_input cC sC uC vC aC cE sE uE vE aE <=>
    &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ &3 / &5 <= sC /\
    c977cc_normal cE (--sE) /\
    --cC - sC <= uC /\ uC + aC <= --cC / &2 /\ vC + aC <= sC /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
    ~linside cE sE uE vE aE (&0) (--(&1)) /\
    ~linside cE sE uE vE aE (&1) (--(&1)) /\
    ldisj cC sC uC vC aC cE sE uE vE aE`;;

(* Lean: Faces (structure) *)
let c1092spnp_faces = new_definition
 `c1092spnp_faces (cE:real) (sE:real) (uE:real) (vE:real) (aE:real) <=>
    &0 < --sE /\ (--sE) / cE < &3 / &8 /\ --cE <= vE /\ uE + aE <= cE - sE /\
    uE < --(&13 / &50) * sE /\ vE < --(&13 / &50) * sE - cE /\
    --(&7 / &20) * (cE + sE) <= uE`;;

let C1092SPNP_LIN_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then REAL_ARITH_TAC g else NLIN_TAC ~deg2:false [] g));;

let C1092SPNP_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN
    STRIP_TAC THEN C1092SPNP_LIN_TAC; ALL_TAC];;

let C1092SPNP_HYPS =
  `cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
   c1092spnp_input cC sC uC vC aC cE sE uE vE aE`;;

let C1092SPNP_UNPACK_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spnp_input] o
    check (can (term_match [] `c1092spnp_input a b c d e f g h i j`) o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aC:real = aE` o concl)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

let C1092SPNP_INTRO_TAC = REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SPNP_UNPACK_TAC;;

(* Lean: initial_faces (private) *)
let C1092SPNP_INITIAL_FACES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092spnp_input cC sC uC vC aC cE sE uE vE aE
     ==> --cE <= vE /\ uE + aE <= cE - sE /\ &0 < --sE`,
  C1092SPNP_INTRO_TAC THEN
  C1092SPNP_NFACT_TAC `~linside cE sE uE vE aC (&0) (--(&1))` `--cE <= vE` THEN
  C1092SPNP_NFACT_TAC `~linside cE sE uE vE aC (&1) (--(&1))` `uE + aC <= cE - sE` THEN
  C1092SPNP_LIN_TAC);;

(* the frames, the relative coefficients k, ell and the unit multiples *)
let C1092SPNP_SETUP_TAC =
  SUBGOAL_THEN `c1092onh_frame cC sC /\ c1092onh_frame cE (--sE)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092onh_frame] THEN C1092SPNP_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092NPP_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= cC * cE + sC * sE /\ &0 < --cC * sE + sC * cE` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`cC:real`; `--sE`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`sC:real`; `cE:real`] REAL_LT_MUL) THEN
    REPEAT(ANTS_TAC THENL [C1092SPNP_LIN_TAC; DISCH_TAC]) THEN C1092SPNP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cC * (cE * cE + sE * sE) = cC /\ sC * (cE * cE + sE * sE) = sC /\
                cE * (cC * cC + sC * sC) = cE`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC];;

(* Lean: recipient_axis (private) *)
let C1092SPNP_RECIPIENT_AXIS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092spnp_input cC sC uC vC aC cE sE uE vE aE /\
     --cE <= vE /\ uE + aE <= cE - sE
     ==> ABT_upper cC sC uC vC aC cE sE <= uE`,
  C1092SPNP_INTRO_TAC THEN C1092SPNP_SETUP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092NPPT_POSITIVE_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `false ==> p`) THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                  `cC * cE + sC * sE`; `--cC * sE + sC * cE`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SPNP_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cC * cE + sC * sE`; `uE + aC`; `cE - sE`] REAL_LE_LMUL) THEN
    MP_TAC(SPECL [`--cC * sE + sC * cE`; `vE:real`; `--(&13 / &50) * sE - cE`] REAL_LE_LMUL) THEN
    MP_TAC(SPECL [`aC - &1`; `&1 + cC * cE + sC * sE`] REAL_LT_MUL) THEN
    REPEAT(ANTS_TAC THENL [C1092SPNP_LIN_TAC; DISCH_TAC]) THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092SNP_CURRENT_MARGIN) THEN
    ASM_REWRITE_TAC[c1092snp_Pu; c1092snp_Qu; REAL_POW_2] THEN DISCH_TAC THEN
    C1092SPNP_LIN_TAC;
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`; `--cC`;
                  `--cC * sE + sC * cE`; `--(cC * cE + sC * sE)`] C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SPNP_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`--cC * sE + sC * cE`; `uE:real`; `--(&13 / &50) * sE`] REAL_LE_LMUL) THEN
    MP_TAC(SPECL [`cC * cE + sC * sE`; `--cE`; `vE:real`] REAL_LE_LMUL) THEN
    MP_TAC(SPECL [`aC - &1`; `&1 + cC * cE + sC * sE`] REAL_LT_MUL) THEN
    REPEAT(ANTS_TAC THENL [C1092SPNP_LIN_TAC; DISCH_TAC]) THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092SNP_TRANSVERSE_MARGIN) THEN
    ASM_REWRITE_TAC[c1092snp_Pv; c1092snp_Qv; REAL_POW_2] THEN DISCH_TAC THEN
    C1092SPNP_LIN_TAC]);;

(* Lean: profile *)
let C1092SPNP_PROFILE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092spnp_input cC sC uC vC aC cE sE uE vE aE
     ==> c1092spnp_faces cE sE uE vE aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092SPNP_INITIAL_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092SPNP_RECIPIENT_AXIS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092SPNP_UNPACK_TAC THEN C1092SPNP_SETUP_TAC THEN
  REWRITE_TAC[c1092spnp_faces] THEN
  SUBGOAL_THEN `(--sE) / cE < &3 / &8` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < cE` ASSUME_TAC THENL [C1092SPNP_LIN_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`;
                  `cC * cE + sC * sE`; `--(--cC * sE + sC * cE)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SPNP_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`] C1092SNP_ENVELOPE) THEN
    ASM_REWRITE_TAC[c1092snp_f; c1092snp_B; REAL_POW_2] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`cC * cE + sC * sE`; `--cC - sC`; `uC:real`] REAL_LE_LMUL) THEN
    MP_TAC(SPECL [`--cC * sE + sC * cE`; `vC + aC`; `sC:real`] REAL_LE_LMUL) THEN
    MP_TAC(SPECL [`aC - &1`; `cC * cE + sC * sE + --cC * sE + sC * cE`] REAL_LT_MUL) THEN
    MP_TAC(SPECL [`cE:real`; `&1 + cC * sC - cC - sC`; `&43 / &500`] REAL_LT_LMUL) THEN
    MP_TAC(SPECL [`--sE`; `&6 / &25`; `cC - sC + sC * sC - &13 / &50`] REAL_LE_LMUL) THEN
    REPEAT(ANTS_TAC THENL [C1092SPNP_LIN_TAC; DISCH_TAC]) THEN
    C1092SPNP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&7 / &20) * (cE + sE) <= uE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`--(&7 / &20)`; `--(&7 / &20)`]
      (REWRITE_RULE[ldisj] (ASSUME `ldisj cC sC uC vC aC cE sE uE vE aC`))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[linside] THEN C1092SPNP_LIN_TAC;
    ALL_TAC] THEN
  C1092SPNP_LIN_TAC);;
