(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastRightWall.lean                         *)
(* (N12Compact.C981CompletionLastRightWall).  The actual arbitrary-angle wall *)
(* owner forces the neighbouring central square past sine 1/2.               *)
(* Normal is c977cc_normal, Minor is c981lrs_minor, upper / lower are         *)
(* ABT_upper / ABT_lower, upper_in_bands / lower_in_bands are C981SF_*,       *)
(* faces / upper_wall / alternatives are C981LRF_*, cross_order is            *)
(* C981OS_CROSS_ORDER, bu_/ru_negative/positive are C981LRS_*,               *)
(* ClosedFrames.positive_frame is CLF_POSITIVE_FRAME.  The Lean lets alpha,  *)
(* beta are written out (alpha = cB*cR+sB*sR, beta = cB*sR-sB*cR).           *)
(* Tag C981LRW_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_LastRightFaces.ml";;
needs "n12/geometry/CP_C981_LastRightScalars.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/CP_C981_OppositeSupport.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C981LRW_LIN = NLIN_TAC ~deg2:false [];;

let C981LRW_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C981LRW_LIN; ALL_TAC];;

let C981LRW_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C981LRW_LIN; ALL_TAC];;

(* X * (cR * cR + sR * sR) = X, from the unit normal of R *)
let C981LRW_UNIT tm = SUBGOAL_THEN (mk_eq(mk_binop `( * ):real->real->real` tm
    `cR * cR + sR * sR`, tm)) ASSUME_TAC THENL
  [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC];;

let C981LRW_ABS_EQ = prove
 (`forall x y. &0 <= y /\ (x = y \/ x = --y) ==> abs x = y`, REAL_ARITH_TAC);;

let C981LRW_ABS lhs rhs = SUBGOAL_THEN (mk_eq(mk_comb(`abs`, lhs), rhs))
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [MATCH_MP_TAC C981LRW_ABS_EQ THEN CONJ_TAC THENL
    [C981LRW_LIN; (DISJ1_TAC THEN REAL_ARITH_TAC) ORELSE (DISJ2_TAC THEN REAL_ARITH_TAC)];
   ALL_TAC];;

(* Lean: positive (private) *)
let C981LRW_POSITIVE = prove
 (`forall cB sB uB vB aB cR sR uR vR aR.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cB sB /\ &0 < cR /\ &0 <= sR /\ &1 < aB /\ aB = aR /\
     c981lrs_minor cB sB /\
     (--cB <= uB /\ (&2 / &5) * sB <= vB /\
      uB + aB <= sB - (&2 / &5) * cB /\ vB + aB <= cB + sB) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     (forall x y. linside cR sR uR vR aR x y ==> y <= &2) /\
     linside cR sR uR vR aR (--(&2 / &5)) (&1) /\ linside cR sR uR vR aR (&13 / &50) (&1) /\
     ~linside cR sR uR vR aR (&2 / &5) (&1) /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C981LRF_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C981LRF_UPPER_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* own: strict_bounds of B at the marker in direction (cR, sR) *)
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `--(&7 / &20)`; `&7 / &20`; `cR:real`; `sR:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aR`)) THEN
  C981LRS_MINOR_TAC THEN C981LRS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C981SF_LOWER_IN_BANDS; C981SF_UPPER_IN_BANDS]) THEN
  SUBGOAL_THEN `&0 < cB /\ &0 < sB` STRIP_ASSUME_TAC THENL [CONJ_TAC THEN C981LRW_LIN; ALL_TAC] THEN
  C981LRW_PROD `&0 < cB * cR` THEN C981LRW_PROD `&0 <= sB * sR` THEN
  C981LRW_FACT `&0 < cB * cR + sB * sR` THEN
  SUBGOAL_THEN `cR <= &1 /\ sR <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `cR - &1`; SQ_NONNEG `sR - &1`]; ALL_TAC] THEN
  C981LRW_ABS `cB * cR + sB * sR` `cB * cR + sB * sR` THEN
  C981LRW_ABS `cR * cB + sR * sB` `cB * cR + sB * sR` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  SUBGOAL_THEN `uR + aB <= (&2 / &5) * cR + sR \/ cR - (&2 / &5) * sR <= vR` MP_TAC THENL
   [ASM_CASES_TAC `uR + aB <= (&2 / &5) * cR + sR` THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN C981LRW_LIN; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_neg o concl)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (can (term_match [] `ldisj a b c d e f g h i j`) o concl)) THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [(* upperU *)
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [(* bu *)
      ASM_CASES_TAC `cB * sR - sB * cR <= &0` THENL
       [C981LRW_ABS `--cB * sR + sB * cR` `--(cB * sR - sB * cR)` THEN
        C981LRW_ABS `--cR * sB + sR * cB` `--(cB * sR - sB * cR)` THEN
        MP_TAC(SPECL [`cB:real`; `sB:real`; `cR:real`; `sR:real`] C981OS_CROSS_ORDER) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN C981LRW_LIN; STRIP_TAC] THEN
        C981LRW_PROD `&0 <= (cB * cR + sB * sR) * ((&2 / &5) * cR + sR - aB - uR)` THEN
        C981LRW_PROD `&0 <= --(cB * sR - sB * cR) * (cR - (&13 / &50) * sR - vR)` THEN
        C981LRW_PROD `&0 < (cB * cR + sB * sR) * (aB - &1)` THEN
        C981LRW_UNIT `(&2 / &5) * cB + sB` THEN
        C981LRW_FACT `&1 < (&7 / &5) * cB + sB - (cB * cR + sB * sR) -
                      (&7 / &50) * (cB * sR - sB * cR) * sR` THEN
        C981LRW_PROD `&0 <= (&1 - cB) * (&1 - cR)` THEN
        C981LRW_PROD `&0 <= sR * (sB - sR)` THEN
        C981LRW_PROD `&0 <= cR * (&1 - cR)` THEN
        C981LRW_FACT `cB <= cB * cR + sB * sR` THEN
        C981LRW_PROD `&0 <= sB * (&1 - cR)` THEN
        C981LRW_PROD `&0 <= cB * sR` THEN
        C981LRW_FACT `--(cB * sR - sB * cR) <= sB` THEN
        C981LRW_PROD `&0 <= (&1 / &2 - --(cB * sR - sB * cR)) * sR` THEN
        C981LRW_LIN;
        RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
        C981LRW_ABS `--cB * sR + sB * cR` `cB * sR - sB * cR` THEN
        C981LRW_ABS `--cR * sB + sR * cB` `cB * sR - sB * cR` THEN
        C981LRW_PROD `&0 <= (cB * cR + sB * sR) * ((&2 / &5) * cR + sR - aB - uR)` THEN
        C981LRW_PROD `&0 <= (cB * sR - sB * cR) * (vR + aB - cR - (&2 / &5) * sR)` THEN
        C981LRW_PROD `&0 < (cB * cR + sB * sR) * (aB - &1)` THEN
        C981LRW_UNIT `(&2 / &5) * cB + sB` THEN
        C981LRW_FACT `&1 < (&7 / &5) * cB + sB - (cB * cR + sB * sR) -
                      (&4 / &5) * (cB * sR - sB * cR) * sR` THEN
        MP_TAC(SPECL [`cR:real`; `sR:real`; `cB:real`; `sB:real`] C981OS_CROSS_ORDER) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN C981LRW_LIN; STRIP_TAC] THEN
        C981LRW_PROD `&0 <= cR * (&1 - (&4 / &5) * cR)` THEN
        C981LRW_UNIT `&4 / &5` THEN
        C981LRW_FACT `&7 / &5 - cR - (&4 / &5) * sR * sR <= &3 / &5` THEN
        C981LRW_PROD `&0 <= sR * (&1 - cR)` THEN
        C981LRW_FACT `&1 - sR + (&4 / &5) * cR * sR <= &453 / &500` THEN
        C981LRW_PROD `&0 <= cB * (&3 / &5 - (&7 / &5 - cR - (&4 / &5) * sR * sR))` THEN
        C981LRW_PROD `&0 <= sB * (&453 / &500 - (&1 - sR + (&4 / &5) * cR * sR))` THEN
        C981LRW_LIN];
      (* ru *)
      SUBGOAL_THEN `(&3 / &4) * cR + (&13 / &20) * sR <= &1` ASSUME_TAC THENL
       [NLIN_TAC [SQ_NONNEG `(&13 / &20) * cR - (&3 / &4) * sR`]; ALL_TAC] THEN
      ASM_CASES_TAC `cB * sR - sB * cR <= &0` THENL
       [C981LRW_ABS `--cR * sB + sR * cB` `--(cB * sR - sB * cR)`;
        RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
        C981LRW_ABS `--cR * sB + sR * cB` `cB * sR - sB * cR`] THEN
      C981LRW_LIN];
    (* lowerV *)
    SUBGOAL_THEN `&0 < sR` ASSUME_TAC THENL
     [ASM_CASES_TAC `sR = &0` THENL [ALL_TAC; C981LRW_LIN] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      C981LRW_PROD `&0 <= cR * (vR - cR)` THEN
      C981LRW_PROD `&0 < cR * (aB - &1)` THEN
      C981LRW_PROD `&0 <= cR * (&1 - cR)` THEN
      C981LRW_LIN; ALL_TAC] THEN
    ASM_CASES_TAC `cB * sR - sB * cR <= &0` THENL
     [C981LRW_ABS `--cB * sR + sB * cR` `--(cB * sR - sB * cR)` THEN
      C981LRW_ABS `--cR * sB + sR * cB` `--(cB * sR - sB * cR)` THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [(* bu *)
        C981LRW_PROD `&0 <= sR * ((cB * cR + sB * sR) * uR - (cB * sR - sB * cR) * vR - (aB - cB))` THEN
        C981LRW_PROD `&0 <= (cB * cR + sB * sR) * (&2 - sR * (uR + aB) - cR * (vR + aB))` THEN
        C981LRW_PROD `&0 <= cB * (vR - (cR - (&2 / &5) * sR))` THEN
        C981LRW_PROD `&0 < (cB * cR + sB * sR) * (cR + sR)` THEN
        C981LRW_PROD `&0 < (sR + (cB * cR + sB * sR) * (cR + sR)) * (aB - &1)` THEN
        C981LRW_UNIT `cB * vR` THEN
        MATCH_MP_TAC(SPECL [`cR:real`; `sR:real`; `cB:real`; `sB:real`] C981LRS_BU_NEGATIVE) THEN
        ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN C981LRW_LIN;
        (* ru *)
        C981LRW_PROD `&0 <= (cB * cR + sB * sR) * (uB + cB)` THEN
        C981LRW_PROD `&0 <= --(cB * sR - sB * cR) * (cB + sB - aB - vB)` THEN
        C981LRW_FACT `(cB * cR + sB * sR) * (aB - cB) + (cB * sR - sB * cR) * (cB + sB - aB) <= uR` THEN
        C981LRW_PROD `&0 <= sR * (uR - ((cB * cR + sB * sR) * (aB - cB) +
                                       (cB * sR - sB * cR) * (cB + sB - aB)))` THEN
        C981LRW_PROD `&0 <= cR * (vR - (cR - (&2 / &5) * sR))` THEN
        C981LRW_PROD `&0 <= sR * ((cB * cR + sB * sR) - (cB * sR - sB * cR))` THEN
        C981LRW_PROD `&0 < (sR * ((cB * cR + sB * sR) - (cB * sR - sB * cR)) + cR + sR) * (aB - &1)` THEN
        MP_TAC(SPECL [`cR:real`; `sR:real`; `cB:real`; `sB:real`] C981LRS_RU_NEGATIVE) THEN
        ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN C981LRW_LIN];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      C981LRW_ABS `--cB * sR + sB * cR` `cB * sR - sB * cR` THEN
      C981LRW_ABS `--cR * sB + sR * cB` `cB * sR - sB * cR` THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [(* bu *)
        C981LRW_PROD `&0 <= sR * ((cB * cR + sB * sR) * uR - (cB * sR - sB * cR) * (vR + aB) - (aB - cB))` THEN
        C981LRW_PROD `&0 <= (cB * cR + sB * sR) * (&2 - sR * (uR + aB) - cR * (vR + aB))` THEN
        C981LRW_PROD `&0 <= cB * (vR - (cR - (&2 / &5) * sR))` THEN
        C981LRW_PROD `&0 < (cB * cR + sB * sR) * (cR + sR)` THEN
        C981LRW_PROD `&0 <= sR * (cB * sR - sB * cR)` THEN
        C981LRW_PROD `&0 < (sR + (cB * cR + sB * sR) * (cR + sR) + sR * (cB * sR - sB * cR)) * (aB - &1)` THEN
        C981LRW_UNIT `cB * vR` THEN
        MATCH_MP_TAC(SPECL [`cR:real`; `sR:real`; `cB:real`; `sB:real`] C981LRS_BU_POSITIVE) THEN
        ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN C981LRW_LIN;
        (* ru *)
        C981LRW_PROD `&0 <= (cB * cR + sB * sR) * (uB + cB)` THEN
        C981LRW_PROD `&0 <= (cB * sR - sB * cR) * (vB - (&2 / &5) * sB)` THEN
        C981LRW_FACT `(cB * cR + sB * sR) * (aB - cB) + (cB * sR - sB * cR) * (aB + (&2 / &5) * sB) <= uR` THEN
        C981LRW_PROD `&0 <= sR * (uR - ((cB * cR + sB * sR) * (aB - cB) +
                                       (cB * sR - sB * cR) * (aB + (&2 / &5) * sB)))` THEN
        C981LRW_PROD `&0 <= cR * (vR - (cR - (&2 / &5) * sR))` THEN
        C981LRW_PROD `&0 <= sR * ((cB * cR + sB * sR) + (cB * sR - sB * cR))` THEN
        C981LRW_PROD `&0 < (sR * ((cB * cR + sB * sR) + (cB * sR - sB * cR)) + cR + sR) * (aB - &1)` THEN
        MP_TAC(SPECL [`cR:real`; `sR:real`; `cB:real`; `sB:real`] C981LRS_RU_POSITIVE) THEN
        ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN C981LRW_LIN]]]);;

(* Lean: angle *)
let C981LRW_ANGLE = prove
 (`forall cB sB uB vB aB cR sR uR vR aR.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cB sB /\ &1 < aB /\ aB = aR /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&13 / &50) /\ linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     ~linside cB sB uB vB aB (--(&1)) (&0) /\ ~linside cB sB uB vB aB (--(&2 / &5)) (&0) /\
     ~linside cB sB uB vB aB (--(&1)) (&1) /\ ~linside cB sB uB vB aB (--(&2 / &5)) (&1) /\
     (forall x y. linside cR sR uR vR aR x y ==> y <= &2) /\
     linside cR sR uR vR aR (--(&2 / &5)) (&1) /\ linside cR sR uR vR aR (&13 / &50) (&1) /\
     ~linside cR sR uR vR aR (&2 / &5) (&1) /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> &1 / &2 < sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aR`)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C981LRF_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `c981lrs_minor cB sB` ASSUME_TAC THENL
   [MATCH_MP_TAC C981LRS_MINOR THEN ASM_REWRITE_TAC[] THEN C981LRW_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cQ:real` (X_CHOOSE_THEN `sQ:real` (X_CHOOSE_THEN `uQ:real`
    (X_CHOOSE_THEN `vQ:real` (X_CHOOSE_THEN `aQ:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aQ:real = aB`)) THEN
  MATCH_MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                      `cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aB:real`] C981LRW_POSITIVE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[ldisj]);;
