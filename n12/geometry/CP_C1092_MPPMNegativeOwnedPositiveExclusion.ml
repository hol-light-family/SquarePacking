(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeOwnedPositiveExclusion.lean  *)
(* (namespace N12Compact.C1092MPPMNegativeOwnedPositiveExclusion).  Raw      *)
(* NEGATIVE-OWNED-POSITIVE-OWNED-EXCLUSION Theorem 1.  Squares C, E, B as in *)
(* CP_C1092_MPPMNegativeForwardFaces (c1092nff_input); Scalars: C1092NOPE_*; *)
(* MPPMNegativeForward.source_profile / axes / target_support:              *)
(* C1092NFF_SOURCE_PROFILE / C1092NFW_AXES / C1092NFW_TARGET_SUPPORT;       *)
(* C1092WholeSupports.lower_pn: C1092WS_LOWER_PN; TwoFifths.Support.        *)
(* upper_pos_neg: C1092TFSU_UPPER_POS_NEG.                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveExclusionScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeForward.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;

let C1092NOPX_SQS = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                     `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

let C1092NOPX_HYPS = `cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB`;;

(* Lean: Input (structure, extends MPPMNegativeForward.Input) *)
let c1092nopx_input = new_definition
 `c1092nopx_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB <=>
    c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
    &0 < sE /\ sE / (&1 + cE) <= &7 / &32 /\
    ~linside cE sE uE vE aE (&1) (--(&1)) /\
    ~linside cE sE uE vE aE (&1) (--(&14 / &25)) /\
    ldisj cE sE uE vE aE cB sB uB vB aB`;;

let C1092NOPX_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (can (find_term ((=) `linside`)) t && not (mem t keep))
    then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let C1092NOPX_SETUP_TAC =
  REWRITE_TAC[IMP_CONJ; c1092nopx_input; c1092nff_input] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092NFF_NORMAL_TAC;;

(* Lean: target_faces *)
let C1092NOPX_TARGET_FACES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nopx_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB
     ==> --sE <= uE /\ --cE - sE <= vE /\ uE + aE <= cE - &14 / &25 * sE`,
  REPEAT GEN_TAC THEN C1092NOPX_SETUP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] C1092NOPE_RECIPIENT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  let npxB0 = `linside cE sE uE vE aC (&13 / &50) (--(&1))`
  and npxB1 = `linside cE sE uE vE aC (&2 / &5) (--(&1))`
  and npxIn = `linside cE sE uE vE aC (&0) (--(&13 / &50))`
  and npxTg = `linside cE sE uE vE aC (&7 / &20) (--(&7 / &20))` in
  SUBGOAL_THEN `--sE <= uE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `ldisj cE sE uE vE aC cB sB uB vB aB` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `--(&1)`]) THEN ASM_REWRITE_TAC[] THEN
    C1092NOPX_KEEP_TAC [npxB0; npxIn]; ALL_TAC] THEN
  SUBGOAL_THEN `--cE - sE <= vE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NOPX_KEEP_TAC [`~linside cE sE uE vE aC (&1) (--(&1))`; npxB1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092NOPX_KEEP_TAC [`~linside cE sE uE vE aC (&1) (--(&14 / &25))`; npxB1; npxTg]);;

let C1092NOPX_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: impossible *)
let C1092NOPX_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nopx_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092NOPX_SQS C1092NOPX_TARGET_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092nopx_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB` THEN
    SIMP_TAC[c1092nopx_input]; ALL_TAC] THEN
  MP_TAC(SPECL C1092NOPX_SQS C1092NFF_SOURCE_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL C1092NOPX_SQS C1092NFW_TARGET_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL C1092NOPX_SQS C1092NFW_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `c1092nopx_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB` THEN
  REWRITE_TAC[c1092nopx_input; c1092nff_input] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092NFF_NORMAL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092nff_sourceProfile] o
    check (fun th -> can (term_match [] `c1092nff_sourceProfile a b c d e`) (concl th))) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] C1092NOPE_RECIPIENT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092NOPX_PROD `&0 < cE * (cC + sC)` THEN
  C1092NOPX_PROD `&0 <= --sC * (cE - sE)` THEN
  C1092NOPX_PROD `&0 < --sC * cE` THEN
  C1092NOPX_PROD `&0 <= cC * sE` THEN
  SUBGOAL_THEN `&0 < cC * cE + sC * sE /\ &0 < cC * sE - sC * cE` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092NOPX_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) + (cC * sE - sC * cE))` THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                  `cC * cE + sC * sE`; `--(cC * sE - sC * cE)`] C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    C1092NOPX_PROD `&0 <= (cC * cE + sC * sE) * ((cE - &14 / &25 * sE) - (uE + aC))` THEN
    C1092NOPX_PROD `&0 <= (cC * sE - sC * cE) * (vE - (--cE - sE))` THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `sE:real`] C1092NOPE_LONGITUDINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[c1092nope_Pu; c1092nope_Qu] THEN DISCH_TAC THEN
    SUBGOAL_THEN `cC * (cE * cE + sE * sE) = cC /\ sC * (cE * cE + sE * sE) = sC` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      not (can (find_term ((=) `linside`)) (concl th)) && not (is_forall (concl th)) &&
      not (can (find_term ((=) `ldisj`)) (concl th)))) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `linside cE sE uE vE aC (&0) (--(&13 / &50))` THEN
    REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `sE:real`; `--cE`;
                  `cC * sE - sC * cE`; `--(cC * cE + sC * sE)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    C1092NOPX_PROD `&0 <= (cC * sE - sC * cE) * (uC - --cC)` THEN
    C1092NOPX_PROD `&0 <= (cC * cE + sC * sE) * (&7 / &20 * (cC + sC) - (vC + aC))` THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `sE:real`] C1092NOPE_TRANSVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[c1092nope_Pf; c1092nope_Qf] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sE * (cC * cC + sC * sC) = sE` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      not (can (find_term ((=) `linside`)) (concl th)) && not (is_forall (concl th)) &&
      not (can (find_term ((=) `ldisj`)) (concl th)))) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;
