(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalBottomNegative.lean       *)
(* (N12Compact.C1092MPPMInwardFinal.BottomAngle; Lean header: "Source only, *)
(* uncompiled").  Both relative-angle orders for the actual nonpositive      *)
(* bottom square of INWARD-BOTTOM-ANGLE.  Conventions of                     *)
(* MPPMInwardFinalBottomData.ml (C = cC .. aC, B = cB .. aB, Input =         *)
(* c1092ifbd_input); half is C1092WPS_half; WholeSupports lower_np / lower_nn *)
(* / upper_np: C1092WS_*; TwoFifths.Support upper_pos_pos:                   *)
(* C1092TFSU_UPPER_POS_POS; BottomScalars: C1092IFBS_*.  Tag C1092IFBN_.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomData.ml";;

(* Lean: negative_coefficients *)
let C1092IFBN_NEGATIVE_COEFFICIENTS = prove
 (`forall cC sC cB sB. c977cc_normal cC (--sC) /\ c977cc_normal cB (--sB)
     ==> &0 < cC * cB + sC * sB /\ cC * cB + sC * sB <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cB:real`; `--sB`] C1092IFBS_RELATIVE_UNIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cC * cB /\ &0 <= --sC * --sB` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC [SQ_NONNEG `cC * --sB - --sC * cB`; SQ_NONNEG `cC * cB + sC * sB - &1`]);;

let C1092IFBN_OPEN_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifbd_input] o
    check (can (term_match [] `c1092ifbd_input a b c d e f g h i j`) o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C1092PRS_NORMAL_TAC;;

let C1092IFBN_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092IFBD_CENTRAL_FACES) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092IFBD_NEGATIVE_WALL_HEIGHT) THEN
  ASM_REWRITE_TAC[c1092ifbd_faces] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092IFBN_OPEN_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `sB:real`] C1092IFBN_NEGATIVE_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* Lean: negative_v *)
let C1092IFBN_NEGATIVE_V = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c977cc_normal cB (--sB) /\\ C1092WPS_half cC (--sC) <= &1 - cC - (&2 / &5) * sC /\\ vB + aB <= ABT_lower cC sC uC vC aC (--sB) cB ==> F"
   C1092IFBD_VARS C1092IFBD_HYP),
  C1092IFBN_SETUP_TAC THEN
  ASM_CASES_TAC `--(cC:real) * sB + sC * cB <= &0` THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                  `--cC * sB + sC * cB`; `cC * cB + sC * sB`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cB:real`; `--sB`; `&1 - cC - (&2 / &5) * sC`]
      C1092IFBS_NEGATIVE_BEFORE_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= --(--(cC:real) * sB + sC * cB) * (uC - (--cC - (&2 / &5) * sC)) /\
                  &0 <= (cC * cB + sC * sB) * (--aC - vC) /\
                  &0 < ((aC:real) - &1) * ((cC * cB + sC * sB) - (--cC * sB + sC * cB))`
      STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                  `--cC * sB + sC * cB`; `cC * cB + sC * sB`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cB:real`; `--sB`] C1092IFBS_NEGATIVE_AFTER_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= (--(cC:real) * sB + sC * cB) * (--cC / &2 - uC) /\
                  &0 <= (cC * cB + sC * sB) * (--aC - vC) /\
                  &0 < ((aC:real) - &1) * (cC * cB + sC * sB)`
      STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: negative_central *)
let C1092IFBN_NEGATIVE_CENTRAL = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c977cc_normal cB (--sB) /\\ ABT_upper cB sB uB vB aB (--sC) cC <= vC ==> F"
   C1092IFBD_VARS C1092IFBD_HYP),
  C1092IFBN_SETUP_TAC THEN
  SUBGOAL_THEN `--(&1) < ABT_upper cB sB uB vB aC (--sC) cC` MP_TAC THENL
   [ALL_TAC; RASM_ARITH_TAC] THEN
  C1092IFBD_PT_TAC [`linside cB sB uB vB aC (&0) (--(&543 / &500))`;
                    `linside cB sB uB vB aC (--(&14 / &25)) (--(&1))`] THEN
  SUBGOAL_THEN `&0 < (cC * cB + sC * sB) * (vB + aC + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= --(sC:real) * cB + cC * sB` THENL
   [MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--sC`; `cC:real`;
                  `--sC * cB + cC * sB`; `cC * cB + sC * sB`] C1092TFSU_UPPER_POS_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `&0 <= (--(sC:real) * cB + cC * sB) * (uB + aC)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--sC`; `cC:real`;
                `--sC * cB + cC * sB`; `cC * cB + sC * sB`] C1092WS_UPPER_NP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `--(sB:real) <= (&14 / &25) * cB` THENL
   [SUBGOAL_THEN `&0 <= --(--(sC:real) * cB + cC * sB) * --uB` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= --(--(sC:real) * cB + cC * sB) * (--(&14 / &25) * cB - sB - uB) /\
    &0 < (cC * cB + sC * sB) * (vB + aC + (&543 / &500) * cB)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `--sB`] C1092IFBS_NEGATIVE_CENTRAL_NORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`;
                `&1 + (&43 / &500) * cB pow 2 - (&14 / &25) * cB * --sB`;
                `(&14 / &25) * cB pow 2 + (&43 / &500) * cB * --sB`] C1092IFBS_DOT_LE_ONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(--(sC:real) * cB + cC * sB) * (--(&14 / &25) * cB - sB) +
    (cC * cB + sC * sB) * (--(&543 / &500) * cB) =
    --cC * (&1 + (&43 / &500) * cB pow 2 - (&14 / &25) * cB * --sB) +
    sC * ((&14 / &25) * cB pow 2 + (&43 / &500) * cB * --sB)` ASSUME_TAC THENL
   [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: nonpositive_impossible *)
let C1092IFBN_NONPOSITIVE_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c977cc_normal cB (--sB) /\\ C1092WPS_half cC (--sC) pow 2 - &2 * C1092WPS_half cC (--sC) + &1 / &5 <= &0 ==> F"
   C1092IFBD_VARS C1092IFBD_HYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal cC (--sC)` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092ifbd_input cC sC uC vC aC cB sB uB vB aB` THEN
    REWRITE_TAC[c1092ifbd_input] THEN STRIP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFBS_BAD_ARC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092IFBD_SEPARATORS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal cB (--sB)` THEN
    REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC C1092IFBN_NEGATIVE_CENTRAL THEN
    MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                          `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `cB:real`; `sB:real`]
      C1092IFBD_CONE) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNU) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN
    UNDISCH_TAC `c977cc_normal cB (--sB)` THEN REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC C1092IFBN_NEGATIVE_V THEN
    MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                          `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
