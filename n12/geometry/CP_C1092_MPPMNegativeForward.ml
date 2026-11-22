(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeForward.lean                  *)
(* (N12Compact.C1092MPPMNegativeForward), full local Theorem 2 of           *)
(* NEGATIVE-FORWARD-POSITIVE-H.  Squares C, E, B as in                       *)
(* CP_C1092_MPPMNegativeForwardFaces (tags C1092NFF, c1092nff); scalars     *)
(* C1092NFS_*; formulas C1092WS_*; upper_neg/lower_neg                       *)
(* C1092MCSUP_NEGATIVE_SUPPORT; SAT step ABT_FOUR_AXES; centerX/Y lcx/lcy.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeForwardFaces.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;

let C1092NFW_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092NFW_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092NFW_LP_TAC; ALL_TAC];;

let C1092NFW_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
                  FIRST [REAL_ARITH_TAC; C1092NFW_LP_TAC]; DISCH_TAC];;

let C1092NFW_SQS = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                    `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

let C1092NFW_SQS' = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                     `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

(* the cone of separating directions (local `cone` of axes) *)
let C1092NFW_CONE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx /\ &0 < nx - ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092nff_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `--(&7 / &20)`; `--(&7 / &20)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                `&7 / &20`; `--(&7 / &20)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `--(&13 / &50)`; `&0`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                `&0`; `--(&13 / &50)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092NFW_LP_TAC);;

let C1092NFW_CONE_REV = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cE sE uE vE aE nx ny <= ABT_lower cC sC uC vC aC nx ny
     ==> &0 < --nx /\ &0 < --nx - --ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092NFW_CONE THEN MAP_EVERY EXISTS_TAC C1092NFW_SQS THEN
  ASM_REWRITE_TAC[C1092MCSUP_NEGATIVE_SUPPORT] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN ASM_REAL_ARITH_TAC);;

(* Lean: axes *)
let C1092NFW_AXES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB
     ==> uC + aC <= ABT_lower cE sE uE vE aE cC sC \/
         ABT_upper cC sC uC vC aC cE sE <= uE \/
         ABT_upper cC sC uC vC aC sE (--cE) <= --(vE + aE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB`) THEN
  REWRITE_TAC[c1092nff_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092NFF_NORMAL_TAC THEN
  let usecone th nx ny =
    MP_TAC(SPECL (C1092NFW_SQS' @ [nx; ny]) th) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     RASM_ARITH_TAC;
     RASM_ARITH_TAC] in
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         usecone C1092NFW_CONE_REV `cC:real` `sC:real`;
         usecone C1092NFW_CONE `--sC:real` `cC:real`;
         usecone C1092NFW_CONE_REV `--sC:real` `cC:real`;
         usecone C1092NFW_CONE_REV `cE:real` `sE:real`;
         usecone C1092NFW_CONE `--sE:real` `cE:real`;
         DISJ2_TAC THEN DISJ2_TAC THEN
         MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `sE:real`; `--cE:real`]
           C1092MCSUP_NEGATIVE_SUPPORT) THEN
         MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sE:real`; `--cE:real`]
           C1092MCSUP_NEGATIVE_SUPPORT) THEN
         ASM_REWRITE_TAC[REAL_NEG_NEG] THEN RASM_ARITH_TAC]);;

(* Lean: target_support *)
let C1092NFW_TARGET_SUPPORT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092nff_sourceProfile cC sC uC vC aC
     ==> --(&13 / &50) * sE < ABT_upper cC sC uC vC aC cE sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092NFW_USE C1092NFF_CENTER_FLOOR C1092NFW_SQS THEN
  MP_TAC(ASSUME `c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB`) THEN
  REWRITE_TAC[c1092nff_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092NFF_NORMAL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092nff_sourceProfile] o
    check (fun th -> can (term_match [] `c1092nff_sourceProfile a b c d e`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092NFW_PROD `&0 < cE * (cC - --sC)` THEN C1092NFW_PROD `&0 <= --sC * (cE - sE)` THEN
  C1092NFW_PROD `&0 < --sC * cE` THEN C1092NFW_PROD `&0 <= cC * sE` THEN
  SUBGOAL_THEN `&0 < cC * cE - --sC * sE /\ &0 < cC * sE + --sC * cE` STRIP_ASSUME_TAC
  THENL [C1092NFW_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cC sC uC vC aC cE sE =
                cE * lcx cC sC uC vC aC + sE * lcy cC sC uC vC aC +
                aC * ((cC * cE - --sC * sE) + (cC * sE + --sC * cE)) / &2` ASSUME_TAC THENL
  [REWRITE_TAC[ABT_upper; tss_support_radius] THEN
   SUBGOAL_THEN `abs(cE * cC + sE * sC) = cC * cE - --sC * sE /\
                 abs(--cE * sC + sE * cC) = cC * sE + --sC * cE`
   (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o AP_TERM `(*) (cC:real)` o check (fun th ->
    is_eq(concl th) && lhand(concl th) = `ABT_upper cC sC uC vC aC cE sE`)) THEN
  FIRST_ASSUM(ASSUME_TAC o AP_TERM `(*) (cE:real)` o check (fun th ->
    concl th = `cC * lcx cC sC uC vC aC + sC * lcy cC sC uC vC aC = uC + aC / &2`)) THEN
  C1092NFW_PROD `&0 <= cE * (uC + cC)` THEN
  C1092NFW_PROD `&0 < (cC * sE + --sC * cE) *
                       (lcy cC sC uC vC aC - (--(&1) + aC * (cC - sC) / &2))` THEN
  C1092NFW_PROD `&0 <= (cC * sE + --sC * cE) * (cC + --sC)` THEN
  C1092NFW_PROD `&0 < cC * ((cC * cE - --sC * sE) + (cC * sE + --sC * cE))` THEN
  C1092NFW_PROD `&0 < (aC - &1) * ((cC * sE + --sC * cE) * (cC + --sC) + cE +
                    cC * ((cC * cE - --sC * sE) + (cC * sE + --sC * cE)))` THEN
  C1092NFW_PROD `&0 < (&1 - cC) * cE * (&1 - --sC)` THEN
  C1092NFW_PROD `&0 <= cC * sE * (cC - &37 / &50)` THEN
  SUBGOAL_THEN `cE * (cC * cC + sC * sC) = cE` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cC * (ABT_upper cC sC uC vC aC cE sE + (&13 / &50) * sE)`
  ASSUME_TAC THENL [C1092NFW_LP_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092NFW_PROD `&0 <= cC * --(ABT_upper cC sC uC vC aC cE sE + (&13 / &50) * sE)` THEN
  C1092NFW_LP_TAC);;

(* Lean: point *)
let C1092NFW_POINT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB
     ==> linside cE sE uE vE aE (&1 / &2) (--(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092NFW_USE C1092NFF_SOURCE_PROFILE C1092NFW_SQS THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  C1092NFW_USE C1092NFF_TARGET_LOWER C1092NFW_SQS THEN
  C1092NFW_USE C1092NFW_TARGET_SUPPORT C1092NFW_SQS THEN
  C1092NFW_USE C1092NFW_AXES C1092NFW_SQS THEN
  MP_TAC(ASSUME `c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB`) THEN
  REWRITE_TAC[c1092nff_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092NFF_NORMAL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092nff_sourceProfile] o
    check (fun th -> can (term_match [] `c1092nff_sourceProfile a b c d e`) (concl th))) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) then th
                           else REWRITE_RULE[linside] th) THEN
  C1092NFW_PROD `&0 < cE * (cC - --sC)` THEN C1092NFW_PROD `&0 <= --sC * (cE - sE)` THEN
  C1092NFW_PROD `&0 < --sC * cE` THEN C1092NFW_PROD `&0 <= cC * sE` THEN
  SUBGOAL_THEN `&0 < cC * cE - --sC * sE /\ &0 < cC * sE + --sC * cE` STRIP_ASSUME_TAC
  THENL [C1092NFW_LP_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `ABT_lower cE sE uE vE aC cC sC`)) (concl th))) THENL
  [C1092NFW_USE C1092WS_LOWER_PN
     [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
      `cC * cE - --sC * sE`; `--(cC * sE + --sC * cE)`] THEN
   C1092NFW_PROD `&0 < (cC * cE - --sC * sE) * (--(&13 / &50) * sE - uE)` THEN
   C1092NFW_PROD `&0 <= (cC * sE + --sC * cE) * (vE - (--cE - sE / &2))` THEN
   C1092NFW_USE C1092NFS_LONGITUDINAL_MARGIN [`cC:real`; `--sC:real`; `cE:real`; `sE:real`] THEN
   C1092NFW_PROD `&0 < (aC - &1) * (&1 + (cC * sE + --sC * cE))` THEN
   C1092NFW_LP_TAC;
   C1092NFW_LP_TAC;
   MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `sE:real`; `--cE:real`]
     C1092WS_FORMULAS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
   SUBGOAL_THEN `max (sE * cC + --cE * sC) (&0) = sE * cC + --cE * sC /\
                 max (--sE * sC + --cE * cC) (&0) = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `max (sE * cC + --cE * sC) (&0) = sE * cC + --cE * sC`;
                               ASSUME `max (--sE * sC + --cE * cC) (&0) = &0`]) THEN
   C1092NFW_PROD `&0 <= (cC * sE + --sC * cE) * (uC + cC)` THEN
   C1092NFW_PROD `&0 <= (cC * cE - --sC * sE) * ((&7 / &20) * (cC + sC) - (vC + aC))` THEN
   C1092NFW_USE C1092NFS_TRANSVERSE_MARGIN [`cC:real`; `--sC:real`; `cE:real`; `sE:real`] THEN
   C1092NFW_PROD `&0 < (aC - &1) * (&1 + (cC * cE - --sC * sE) + (cC * sE + --sC * cE))` THEN
   C1092NFW_LP_TAC]);;
