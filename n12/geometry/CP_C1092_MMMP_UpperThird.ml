(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/UpperThird.lean                     *)
(* (N12Compact.C1092MMMPUpperThird).  The whole local W--N conclusion of     *)
(* NORTHEAST-UPPER-THIRD §4.  OpenSquares W, N are 5-tuples with their       *)
(* invariants as hypotheses; Normal = c977cc_normal; NortheastCore =         *)
(* c1092mtfen_core.  UpperThirdScalars: C1092UTS_*; C977CornerSectorBounds.  *)
(* cosine_order / sine_order: C977CSB_*; EndingAxes.alternatives:            *)
(* C1092MEA_ALTERNATIVES; upper_nn C1092MEA_UPPER_NN; lower_nn / lower_pn /  *)
(* formulas: C1092WS_*; FinalScalars39.own_positive C1092FS39_OWN_POSITIVE.  *)
(* Tag C1092MUT_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_UpperThirdScalars.ml";;
needs "n12/geometry/CP_C1092_MMMP_EndingAxes.ml";;
needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceNortheast.ml";;

(* Lean: sum_cap (private) *)
let C1092MUT_SUM_CAP = prove
 (`forall b t. c977cc_normal b t ==> b + t < &71 / &50`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> concl th = `c977cc_normal b t`)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (b + t - &71 / &50) * (b + t + &71 / &50)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `b - t:real` REAL_LE_SQUARE) THEN RASM_ARITH_TAC);;

let C1092MUT_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: upper_third *)
let C1092MUT_UPPER_THIRD = prove
 (`forall cW sW uW vW aW cN sN uN vN aN.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     &1 < aW /\ aW = aN /\ c977cc_normal cW sW /\ &8 * sW < &7 * cW /\
     linside cW sW uW vW aW (&0) (&0) /\ linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     &23 / &25 < vW + aW /\ aW - cW + (&2 / &5) * sW <= uW + aW /\
     c1092mtfen_core cN sN uN vN aN /\ ldisj cW sW uW vW aW cN sN uN vN aN
     ==> &3 * sN < &1 + cN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aN`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mtfen_core] o
    check (fun th -> concl th = `c1092mtfen_core cN sN uN vN aW`)) THEN
  SUBGOAL_THEN `c977cc_normal cN sN` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`] C1092MEA_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c977cc_normal cW sW` THEN REWRITE_TAC[c977cc_normal] THEN RASM_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] C1092UTS_SHALLOW_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `cN:real`; `sN:real`] C1092UTS_RELATIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`] C1092MUT_SUM_CAP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> concl th = `c977cc_normal cW sW`)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 / &5 <= sN` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `cN:real`; `sN:real`] C977CSB_COSINE_ORDER) THEN
    REWRITE_TAC[prove(`c977cc_normal (&4 / &5) (&3 / &5)`,
      REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV)] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`] C1092UTS_COSINE_CAP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `uN < &21 / &50 /\ &0 <= uN /\ vN < &0 /\ vW < &0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cW sW uW vW aW (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= cN * sW - sN * cW` THENL
   [MP_TAC(SPECL [`cW:real`; `sW:real`; `cN:real`; `sN:real`] C977CSB_SINE_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `cN:real`; `sN:real`] C977CSB_COSINE_ORDER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&11 / &25 < uW + aW` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    C1092MUT_PROD_TAC [`&0 <= (&4 / &5 - cN) * sW`; `&0 <= (sN - &3 / &5) * cW`] THEN
    SUBGOAL_THEN `cN * sW - sN * cW <= &1 / &10` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&49 / &50 < cN * cW + sN * sW` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092MUT_PROD_TAC [`&0 <= (&49 / &50 - (cN * cW + sN * sW)) * (&49 / &50 + (cN * cW + sN * sW))`;
                         `&0 <= (&1 / &10 - (cN * sW - sN * cW)) * (&1 / &10 + (cN * sW - sN * cW))`] THEN
      UNDISCH_TAC `(cN * cW + sN * sW) pow 2 + (sN * cW - cN * sW) pow 2 = &1` THEN
      REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`; `cW:real`; `sW:real`;
                    `cN * cW + sN * sW`; `cN * sW - sN * cW`] C1092WS_LOWER_NN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
      C1092MUT_PROD_TAC [`&0 <= (&1 - (cN * cW + sN * sW)) * uN`;
                         `&0 <= (cN * sW - sN * cW) * --vN`] THEN
      RASM_ARITH_TAC;
      MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `cN:real`; `sN:real`]
        C1092WS_FORMULAS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      SUBGOAL_THEN `max (cN * cW + sN * sW) (&0) = cN * cW + sN * sW /\
                    max (--cN * sW + sN * cW) (&0) = &0` (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
      C1092MUT_PROD_TAC [`&0 < (cN * cW + sN * sW) * (uW + aW - &11 / &25)`;
                         `&0 <= (cN * sW - sN * cW) * --vW`] THEN
      RASM_ARITH_TAC];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`; `cW:real`; `sW:real`;
                  `cN * cW + sN * sW`; `--(sN * cW - cN * sW)`] C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `cN:real`; `sN:real`;
                  `cN * cW + sN * sW`; `sN * cW - cN * sW`] C1092MEA_UPPER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [MP_TAC(SPECL [`cW:real`; `sW:real`; `cN:real`; `sN:real`] C1092FS39_OWN_POSITIVE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C1092FS39_ownMargin] THEN DISCH_TAC] THEN
      C1092MUT_PROD_TAC [`&0 <= (cN * cW + sN * sW) * ((cN + sN - aW) - uN)`;
                         `&0 <= (sN * cW - cN * sW) * ((vN + aW) - (aW + (&39 / &100) * cN - sN))`;
                         `&0 < (aW - &1) * (&1 + (cN * cW + sN * sW) + (sN * cW - cN * sW))`] THEN
      RASM_ARITH_TAC;
      MP_TAC(SPECL [`cW:real`; `sW:real`; `cN:real`; `sN:real`] C1092UTS_NEIGHBOR_POSITIVE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; REWRITE_TAC[c1092uts_margin] THEN DISCH_TAC] THEN
      C1092MUT_PROD_TAC [`&0 <= (cN * cW + sN * sW) * ((uW + aW) - (aW - cW + (&2 / &5) * sW))`;
                         `&0 <= (sN * cW - cN * sW) * ((vW + aW) - &23 / &25)`;
                         `&0 < (aW - &1) * (&1 + (cN * cW + sN * sW))`] THEN
      RASM_ARITH_TAC]]);;
