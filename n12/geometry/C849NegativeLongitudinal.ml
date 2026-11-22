(* ========================================================================= *)
(* Port of Compact/Geometry/C849NegativeLongitudinal.lean                    *)
(* (N12Compact.C849NegativeLongitudinal).  Original-square realization of    *)
(* the two signed-L scalar support bounds.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C849NegativePositiveMargins.ml";;
needs "n12/geometry/C849NegativeLeftScalar.ml";;
needs "n12/geometry/C849NegativeBL.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;

let C849NL_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C849NL_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C849NL_LIN_TAC; DISCH_TAC];;

(* Lean: positive_scalar (private) *)
let C849NL_POSITIVE_SCALAR = prove
 (`forall a c t C S U V W.
     &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\
     &0 < C /\ &0 <= S /\ S <= C /\ C pow 2 + S pow 2 = &1 /\
     a * (C + S) + (&187 / &100) * C * S - (&19 / &25) * S pow 2 <= C * W /\
     U + a <= &2 * c - (&5 / &2) * t /\
     V <= (&33 / &20) * t + (&47 / &20) * c /\
     a * (c + t) - &4 * t <= U /\
     (U + a <= (&113 / &50) * c - &3 * t \/ V + a <= (&113 / &50) * t + &3 * c) /\
     W <= (c * C - t * S) * U + (t * C + c * S) * V
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - t) * C`; `&0 <= t * (C - S)`; `&0 <= c * C - t * S`;
    `&0 <= t * C`; `&0 <= c * S`; `&0 <= t * C + c * S`;
    `&0 <= C * (c * C - t * S)`; `&0 <= C * (t * C + c * S)`] THEN
  SUBGOAL_THEN `C * W <= C * ((c * C - t * S) * U + (t * C + c * S) * V) /\
    (C * (c * C - t * S)) * (U + a) <= (C * (c * C - t * S)) * (&2 * c - (&5 / &2) * t) /\
    (C * (t * C + c * S)) * V <= (C * (t * C + c * S)) * ((&33 / &20) * t + (&47 / &20) * c) /\
    C pow 2 * (c pow 2 + t pow 2) = C pow 2 /\ C * S * (c pow 2 + t pow 2) = C * S`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN C849NL_LIN_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [NLIN_FACTS_TAC [] [`&0 < (a - &1) * (&1 + c + t)`] THEN
    SUBGOAL_THEN `&50 / &63 <= c` ASSUME_TAC THENL [C849NL_LIN_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `S:real`] C849NPM_UPPERU) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[C849NPM_MARGIN0_DEF; C849NPM_MARGIN1_DEF] THEN
    NLIN_FACTS_TAC [] [`&0 < (a - &1) * (C * (c * C - t * S) + C + S)`] THEN
    SUBGOAL_THEN `(C * (c * C - t * S)) * (U + a) <=
                  (C * (c * C - t * S)) * ((&113 / &50) * c - &3 * t)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN C849NL_LIN_TAC;
    MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `S:real`] C849NPM_UPPERV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[C849NPM_MARGIN2_DEF] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 < (a - &1) * (C * ((c * C - t * S) + (t * C + c * S)) + C + S)`] THEN
    SUBGOAL_THEN `(C * (t * C + c * S)) * (V + a) <=
                  (C * (t * C + c * S)) * ((&113 / &50) * t + &3 * c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    C849NL_LIN_TAC]);;

(* Lean: impossible *)
let C849NL_IMPOSSIBLE = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cB /\ sB <= &0 /\ --sB <= cB /\
     &0 < cL /\ abs sL <= cL /\
     &1 < aB /\ aB = aL /\
     lcont cL sL uL vL aL /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     --sL * (&19 / &25) + cL * (&187 / &100) <= vL /\
     uB + aB <= &2 * cB + (&5 / &2) * sB /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     aB * (cB - sB) + &4 * sB <= uB /\
     (uB + aB <= (&113 / &50) * cB + &3 * sB \/
      vB + aB <= --(&113 / &50) * sB + &3 * cB) /\
     uL + aL <= ABT_lower cB sB uB vB aB cL sL
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aL`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS; linside]) THEN
  C849NL_LE_MUL_TAC `cB + sB` `cL:real` THEN C849NL_LE_MUL_TAC `--sB` `cL - sL` THEN
  SUBGOAL_THEN `&0 <= cB * cL + sB * sL` ASSUME_TAC THENL [C849NL_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `cL:real`; `sL:real`]
    FSBL_MINIMUM_PROJECTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `uL + aB <= ABT_lower cB sB uB vB aB cL sL` THEN
  ASM_REWRITE_TAC[ABT_lower] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`]
    FSBL_LEFT_UPPER_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C849NL_LIN_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `~(cL = &0)` ASSUME_TAC THENL [C849NL_LIN_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sL` THENL
   [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `&0 <= sL`)) THEN DISCH_TAC THEN
    SUBGOAL_THEN `aB * (cL + sL) + (&187 / &100) * cL * sL - (&19 / &25) * sL pow 2 <=
                  cL * (uL + aB)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(aB * (&1 + sL / cL) + (&187 / &100) * sL -
                   (&19 / &25) * sL pow 2 / cL) * cL` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `~(cL = &0)` THEN
        CONV_TAC REAL_FIELD;
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN C849NL_LIN_TAC];
      ALL_TAC] THEN
    C849NL_LE_MUL_TAC `cB:real` `sL:real` THEN C849NL_LE_MUL_TAC `--sB` `cL:real` THEN
    SUBGOAL_THEN `abs(cB * sL - sB * cL) = cB * sL - sB * cL`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN C849NL_LIN_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`aB:real`; `cB:real`; `--sB`; `cL:real`; `sL:real`; `uB:real`; `vB:real`;
                  `uL + aB`] C849NL_POSITIVE_SCALAR) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN
      ((ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN NO_TAC) ORELSE
       C849NL_LIN_TAC ORELSE
       (FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
        ((DISJ1_TAC THEN C849NL_LIN_TAC) ORELSE (DISJ2_TAC THEN C849NL_LIN_TAC))));
      REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (MATCH_MP (REAL_ARITH `~(&0 <= x) ==> x <= &0`)
      (ASSUME `~(&0 <= sL)`))) THEN DISCH_TAC THEN
    SUBGOAL_THEN `aB * cL - (&457 / &500) * sL pow 2 + &2 * cL * sL <=
                  cL * (uL + aB)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(aB - (&457 / &500) * sL pow 2 / cL + &2 * sL) * cL` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `~(cL = &0)` THEN
        CONV_TAC REAL_FIELD;
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN C849NL_LIN_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`aB:real`; `cB:real`; `--sB`; `cL:real`; `--sL`; `uB:real`; `vB:real`;
                  `uL + aB`] C849NLS_IMPOSSIBLE) THEN
    SUBGOAL_THEN `abs(--sB * cL - cB * --sL) = abs(cB * sL - sB * cL)` SUBST1_TAC THENL
     [AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN
      ((ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN NO_TAC) ORELSE
       C849NL_LIN_TAC ORELSE
       (FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
        ((DISJ1_TAC THEN C849NL_LIN_TAC) ORELSE (DISJ2_TAC THEN C849NL_LIN_TAC))));
      REWRITE_TAC[]]]);;
