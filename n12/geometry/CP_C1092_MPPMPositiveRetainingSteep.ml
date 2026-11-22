(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveRetainingSteep.lean           *)
(* (N12Compact.C1092MPPMPositiveRetainingSteep), POSITIVE-RETAINING-ANGLE-   *)
(* AND-ORIGINS Theorem 1.  Squares C = cC sC uC vC aC, E = cE sE uE vE aE.  *)
(* Scalars: C1092PRS_* / c1092prs_*; FirstNormals: C1092PRFNT_* /           *)
(* c1092prfnt_input; support formulas C1092WS_*; upper_neg/lower_neg         *)
(* C1092MCSUP_NEGATIVE_SUPPORT; SAT step ABT_FOUR_AXES.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingFirstNormals.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let C1092PRST_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092PRST_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092PRST_LP_TAC; ALL_TAC];;

let C1092PRST_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c1092prs_kappa; c1092prs_sigma] THEN REPEAT CONJ_TAC THEN
                  FIRST [REAL_ARITH_TAC; C1092PRST_LP_TAC]; DISCH_THEN STRIP_ASSUME_TAC];;

let C1092PRST_MM_TAC =
  ASSUM_LIST(fun ths ->
    let mm th = is_eq(concl th) &&
      (let l = lhand(concl th) in is_comb l &&
        (let f,_ = strip_comb l in f = `max:real->real->real` || f = `min:real->real->real`)) in
    let eqs = filter mm ths in
    RULE_ASSUM_TAC(fun th -> if mm th then th else REWRITE_RULE eqs th));;

(* Lean: Input (structure, extends FirstNormals.Input) *)
let c1092prst_input = new_definition
 `c1092prst_input cC sC uC vC aC cE sE uE vE aE <=>
    c1092prfnt_input cC sC uC vC aC cE sE uE vE aE /\
    aC + (&2 / &5) * sC - cC <= vC + aC /\ vE + aE <= &0 /\ &3 / &5 <= sE /\
    aC - cE / &2 <= --uE /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    ldisj cC sC uC vC aC cE sE uE vE aE`;;

let C1092PRST_SQS = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                     `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;

let C1092PRST_SETUP_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092prst_input] o
    check (fun th -> can (term_match [] `c1092prst_input a b c d e f g h i j`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092prfnt_input] o
    check (fun th -> can (term_match [] `c1092prfnt_input a b c d e f g h i j`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* the local `rightward` of first_normals *)
let C1092PRST_RIGHTWARD = prove
 (`forall cC sC uC vC aC cE sE uE vE aE nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092prst_input cC sC uC vC aC cE sE uE vE aE /\ nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRST_SETUP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `--(&7 / &20)`; `--(&7 / &20)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                `&7 / &20`; `--(&7 / &20)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PRST_LP_TAC);;

let C1092PRST_RIGHTWARD_REV = prove
 (`forall cC sC uC vC aC cE sE uE vE aE nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092prst_input cC sC uC vC aC cE sE uE vE aE /\ nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cE sE uE vE aE nx ny <= ABT_lower cC sC uC vC aC nx ny
     ==> &0 < --nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092PRST_RIGHTWARD THEN
  MAP_EVERY EXISTS_TAC (C1092PRST_SQS @ [`--ny:real`]) THEN
  ASM_REWRITE_TAC[C1092MCSUP_NEGATIVE_SUPPORT] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN ASM_REAL_ARITH_TAC);;

(* Lean: first_normals (private) *)
let C1092PRST_FIRST_NORMALS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092prst_input cC sC uC vC aC cE sE uE vE aE
     ==> uC + aC <= ABT_lower cE sE uE vE aE cC sC \/
         ABT_upper cC sC uC vC aC cE sE <= uE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `c1092prst_input cC sC uC vC aC cE sE uE vE aE`) THEN
  REWRITE_TAC[c1092prst_input] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `c1092prfnt_input cC sC uC vC aC cE sE uE vE aE`) THEN
  REWRITE_TAC[c1092prfnt_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns) THEN
  let sqs = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
             `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] in
  let rw th nx ny =
    MP_TAC(SPECL (sqs @ [nx; ny]) th) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     RASM_ARITH_TAC;
     RASM_ARITH_TAC] in
  let tr th nx ny =
    MP_TAC(SPECL sqs th) THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; nx; ny]
      C1092MCSUP_NEGATIVE_SUPPORT) THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; nx; ny]
      C1092MCSUP_NEGATIVE_SUPPORT) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(rand(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC in
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         rw C1092PRST_RIGHTWARD_REV `cC:real` `sC:real`;
         rw C1092PRST_RIGHTWARD `--sC:real` `cC:real`;
         rw C1092PRST_RIGHTWARD_REV `cE:real` `sE:real`;
         rw C1092PRST_RIGHTWARD `--sE:real` `cE:real`;
         tr C1092PRFNT_TRANSVERSE_C `sC:real` `--cC:real`;
         tr C1092PRFNT_TRANSVERSE_E `sE:real` `--cE:real`]);;

(* Lean: no_current (private) *)
let C1092PRST_NO_CURRENT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092prst_input cC sC uC vC aC cE sE uE vE aE
     ==> ~(uC + aC <= ABT_lower cE sE uE vE aE cC sC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRST_SETUP_TAC THEN DISCH_TAC THEN
  C1092PRST_USE C1092PRS_RELATIVE_BOUNDS [`cC:real`; `sC:real`; `cE:real`; `sE:real`] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`]
    C1092WS_FORMULAS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092prs_kappa; c1092prs_sigma]) THEN
  SUBGOAL_THEN `min (cC * cE + sC * sE) (&0) = &0` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PRST_PROD `&0 <= (cC * cE + sC * sE) * (--uE - (aC - cE / &2))` THEN
  ASM_CASES_TAC `&0 <= cC * sE - sC * cE` THENL
  [SUBGOAL_THEN `min (--cC * sE + sC * cE) (&0) = --cC * sE + sC * cE` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092PRST_MM_TAC THEN
   C1092PRST_PROD `&0 <= (cC * sE - sC * cE) * (vE + aC + (&13 / &50) * cE)` THEN
   C1092PRST_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE))` THEN
   C1092PRST_USE C1092PRS_U_POSITIVE [`cC:real`; `sC:real`; `cE:real`; `sE:real`] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[c1092prs_uPlus; c1092prs_kappa; c1092prs_sigma]) THEN
   C1092PRST_LP_TAC;
   SUBGOAL_THEN `min (--cC * sE + sC * cE) (&0) = &0` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092PRST_MM_TAC THEN
   SUBGOAL_THEN `cC * sE - sC * cE <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092PRST_PROD `&0 <= --(cC * sE - sC * cE) * --(vE + aC)` THEN
   C1092PRST_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) - (cC * sE - sC * cE))` THEN
   C1092PRST_USE C1092PRS_U_NEGATIVE [`cC:real`; `sC:real`; `cE:real`; `sE:real`] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[c1092prs_uMinus; c1092prs_kappa; c1092prs_sigma]) THEN
   C1092PRST_LP_TAC]);;

(* Lean: no_recipient (private) *)
let C1092PRST_NO_RECIPIENT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092prst_input cC sC uC vC aC cE sE uE vE aE
     ==> ~(ABT_upper cC sC uC vC aC cE sE <= uE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRST_SETUP_TAC THEN DISCH_TAC THEN
  C1092PRST_USE C1092PRS_RELATIVE_BOUNDS [`cC:real`; `sC:real`; `cE:real`; `sE:real`] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`]
    C1092WS_FORMULAS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092prs_kappa; c1092prs_sigma]) THEN
  SUBGOAL_THEN `max (cE * cC + sE * sC) (&0) = cE * cC + sE * sC` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PRST_PROD `&0 <= (cC * cE + sC * sE) * (uC + aC - (aC - cC - sC))` THEN
  ASM_CASES_TAC `&0 <= cC * sE - sC * cE` THENL
  [SUBGOAL_THEN `max (--cE * sC + sE * cC) (&0) = --cE * sC + sE * cC` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092PRST_MM_TAC THEN
   C1092PRST_PROD `&0 <= (cC * sE - sC * cE) * (vC + aC - (aC + (&2 / &5) * sC - cC))` THEN
   C1092PRST_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) + (cC * sE - sC * cE))` THEN
   C1092PRST_USE C1092PRS_E_POSITIVE [`cC:real`; `sC:real`; `cE:real`; `sE:real`] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[c1092prs_ePlus; c1092prs_kappa; c1092prs_sigma]) THEN
   C1092PRST_LP_TAC;
   SUBGOAL_THEN `max (--cE * sC + sE * cC) (&0) = &0` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092PRST_MM_TAC THEN
   SUBGOAL_THEN `cC * sE - sC * cE <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092PRST_PROD `&0 <= --(cC * sE - sC * cE) * --(vC + aC - sC)` THEN
   C1092PRST_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) - (cC * sE - sC * cE))` THEN
   C1092PRST_USE C1092PRS_E_NEGATIVE [`cC:real`; `sC:real`; `cE:real`; `sE:real`] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[c1092prs_eMinus; c1092prs_kappa; c1092prs_sigma]) THEN
   C1092PRST_LP_TAC]);;

(* Lean: impossible *)
let C1092PRST_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092prst_input cC sC uC vC aC cE sE uE vE aE
     ==> false`,
  MESON_TAC[C1092PRST_FIRST_NORMALS; C1092PRST_NO_CURRENT; C1092PRST_NO_RECIPIENT]);;
