(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCenteredPositiveHeight.lean          *)
(* (namespace N12Compact.C1092MPPMCenteredPositive).                         *)
(* CENTERED-POSITIVE-INWARD-ENDING sections 6--8.  HeightInput is            *)
(* c1092cpha_heightInput; PredecessorPoints is c1092ifcc_predecessorPoints;  *)
(* Normal is c977cc_normal; upper/lower are ABT_upper/ABT_lower;             *)
(* nonnegative/nonpositive_predecessor_faces: C1092IFCC_*; lower_np/lower_nn/*)
(* upper_np/formulas: C1092WS_*; upper_pos_pos (the `formulas` + max step):  *)
(* C1092TFSU_UPPER_POS_POS; dot_le_one / sine_order: C977CSB_*; cap_f0 /     *)
(* cap_g0 / cap_negative_fg: C1092IFCS_*; f, g: c1092mifs_f / c1092mifs_g;   *)
(* the margins and coefficient bounds: C1092CPHS_*.  The Lean local          *)
(* abbreviations k, delta, j are written out.  Tag C1092CPH_.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCenteredPositiveHeightAxes.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCapScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalScalars.ml";;

let C1092CPH_LIN = NLIN_TAC ~deg2:false [];;

let C1092CPH_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC THEN
   C1092CPH_LIN; ALL_TAC];;

let C1092CPH_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092CPH_PRED_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifcc_predecessorPoints] o
    check (fun th -> can (term_match [] `c1092ifcc_predecessorPoints a b c d e`) (concl th)));;

let C1092CPH_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let C1092CPH_FORMULA_TAC th args =
  MP_TAC(SPECL args th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092CPH_LIN;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

let C1092CPH_SQC = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092CPH_SQW = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`];;

let C1092CPH_SETUP_TAC axes faces =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL axes) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] faces) THEN
  UNDISCH_TAC `c1092cpha_heightInput cC sC uC vC aC cW sW uW vW aW` THEN
  REWRITE_TAC[c1092cpha_heightInput] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_TAC THEN
  C1092CPH_PRED_TAC THEN C1092CPH_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < uC + aC` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC];;

let C1092CPH_AXES_SPLIT_TAC =
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `ABT_lower`)) (concl th)));;

(* Lean: positive_height (private) *)
let C1092CPH_POSITIVE_HEIGHT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092cpha_heightInput cC sC uC vC aC cW sW uW vW aW /\ c977cc_normal cW sW
     ==> vC + aC < &17 / &125 + sC`,
  C1092CPH_SETUP_TAC C1092CPHA_POSITIVE_HEIGHT_AXES C1092IFCC_NONNEGATIVE_PREDECESSOR_FACES THEN
  C1092CPH_PROD `&0 < cC * cW` THEN C1092CPH_PROD `&0 <= sC * sW` THEN
  SUBGOAL_THEN `&0 < cC * cW + sC * sW` ASSUME_TAC THENL [C1092CPH_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `sW:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092CPH_AXES_SPLIT_TAC THENL
   [(* current *)
    ASM_CASES_TAC `cC * sW - sC * cW <= &0` THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `sW:real`] C977CSB_SINE_ORDER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      C1092CPH_FORMULA_TAC C1092WS_LOWER_NP
        (C1092CPH_SQW @ [`--sC`; `cC:real`; `cC * sW - sC * cW`; `cC * cW + sC * sW`]) THEN
      C1092CPH_UNFOLD_TAC `linside cW sW uW vW aC (--(&13 / &50)) (&1)` THEN
      SUBGOAL_THEN `vW < &43 / &500 + sC` ASSUME_TAC THENL [C1092CPH_LIN; ALL_TAC] THEN
      C1092CPH_PROD `&0 <= (--(cC * sW - sC * cW)) * (uW + aC + &13 / &50)` THEN
      C1092CPH_PROD `&0 <= sC * (&1 - cW)` THEN C1092CPH_PROD `&0 <= cC * sW` THEN
      C1092CPH_PROD `&0 < (cC * cW + sC * sW) * ((&43 / &500 + sC) - vW)` THEN
      C1092CPH_PROD `&0 <= (&1 - (cC * cW + sC * sW)) * (&43 / &500 + sC)` THEN
      C1092CPH_LIN;
      C1092CPH_FORMULA_TAC C1092WS_LOWER_NN
        (C1092CPH_SQW @ [`--sC`; `cC:real`; `cC * sW - sC * cW`; `cC * cW + sC * sW`]) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
        is_disj(concl th) && not (can (find_term ((=) `ABT_upper`)) (concl th)) &&
        not (can (find_term ((=) `ABT_lower`)) (concl th)))) THENL
       [(* topV *)
        C1092CPH_UNFOLD_TAC `linside cW sW uW vW aC (--(&7 / &20)) (&7 / &20)` THEN
        SUBGOAL_THEN `uW <= &0 /\ vW < &43 / &500` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN C1092CPH_LIN; ALL_TAC] THEN
        C1092CPH_PROD `&0 <= (cC * sW - sC * cW) * (&0 - uW)` THEN
        C1092CPH_PROD `&0 < (cC * cW + sC * sW) * (&43 / &500 - vW)` THEN
        C1092CPH_LIN;
        (* topU *)
        FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN STRIP_ASSUME_TAC) o
          check (fun th -> is_conj(concl th) && is_disj(rand(concl th)))) THEN
        C1092CPH_PROD `&0 <= (cC * sW - sC * cW) * ((&543 / &500) * sW - aC - uW)` THEN
        C1092CPH_PROD `&0 < (aC - &1) * ((cC * sW - sC * cW) + (cC * cW + sC * sW))` THENL
         [C1092CPH_PROD `&0 <= (cC * cW + sC * sW) * (cW + sW - aC - vW)` THEN
          SUBGOAL_THEN `vC + aC < cC * ((cW + sW - &1) pow 2 / &2 + (&43 / &500) * sW pow 2) +
                                  sC * (sW pow 2 + cW - sW - (&43 / &500) * cW * sW)`
            ASSUME_TAC THENL
           [SUBGOAL_THEN `cC * ((cW + sW - &1) pow 2 / &2 + (&43 / &500) * sW pow 2) +
                          sC * (sW pow 2 + cW - sW - (&43 / &500) * cW * sW) =
                          (cC * sW - sC * cW) * ((&543 / &500) * sW - &1) +
                          (cC * cW + sC * sW) * (cW + sW - &1)` SUBST1_TAC THENL
             [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; C1092CPH_LIN];
            ALL_TAC] THEN
          MP_TAC(SPECL [`cW:real`; `sW:real`] C1092IFCS_CAP_F0) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          MP_TAC(SPECL [`cW:real`; `sW:real`] C1092CPHS_POSITIVE_COEFFICIENTS_UPPER) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          C1092CPH_PROD `&0 < cC * (&13 / &100 - ((cW + sW - &1) pow 2 / &2 + (&43 / &500) * sW pow 2))` THEN
          C1092CPH_PROD `&0 <= sC * (&1 - (sW pow 2 + cW - sW - (&43 / &500) * cW * sW))` THEN
          C1092CPH_LIN;
          C1092CPH_PROD `&0 <= (cC * cW + sC * sW) * ((&543 / &500) * cW + sW - aC - vW)` THEN
          SUBGOAL_THEN `vC + aC < cC * (&43 / &500 + (cW + sW - &1) pow 2 / &2) +
                                  sC * (sW pow 2 + cW - sW)` ASSUME_TAC THENL
           [SUBGOAL_THEN `cC * (&43 / &500 + (cW + sW - &1) pow 2 / &2) + sC * (sW pow 2 + cW - sW) =
                          (cC * sW - sC * cW) * ((&543 / &500) * sW - &1) +
                          (cC * cW + sC * sW) * ((&543 / &500) * cW + sW - &1)` SUBST1_TAC THENL
             [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; C1092CPH_LIN];
            ALL_TAC] THEN
          MP_TAC(SPECL [`cW:real`; `sW:real`] C1092IFCS_CAP_G0) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          MP_TAC(SPECL [`cW:real`; `sW:real`] C1092CPHS_POSITIVE_COEFFICIENTS_UPPER) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          C1092CPH_PROD `&0 < cC * (&247 / &2500 - (&43 / &500 + (cW + sW - &1) pow 2 / &2))` THEN
          C1092CPH_PROD `&0 <= sC * (&1 - (sW pow 2 + cW - sW))` THEN
          C1092CPH_LIN]]];
    (* own *)
    ASM_CASES_TAC `cC * sW - sC * cW <= &0` THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `sW:real`] C977CSB_SINE_ORDER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      C1092CPH_PROD `&0 <= (&1 - cC) * (&1 - cW)` THEN
      C1092CPH_PROD `&0 <= cW * (&1 - cW)` THEN
      C1092CPH_PROD `&0 <= sW * (sC - sW)` THEN
      SUBGOAL_THEN `cC <= cC * cW + sC * sW` ASSUME_TAC THENL [C1092CPH_LIN; ALL_TAC] THEN
      C1092CPH_FORMULA_TAC C1092TFSU_UPPER_POS_POS
        (C1092CPH_SQC @ [`--sW`; `cW:real`; `--(cC * sW - sC * cW)`; `cC * cW + sC * sW`]) THEN
      C1092CPH_PROD `&0 <= (--(cC * sW - sC * cW)) * (uC + aC)` THEN
      C1092CPH_PROD `&0 <= (cC * cW + sC * sW) * (vC + aC - (&17 / &125 + sC))` THEN
      C1092CPH_PROD `&0 <= ((cC * cW + sC * sW) - &99 / &100) * (&17 / &125 + sC)` THEN
      SUBGOAL_THEN `vW < &43 / &500 + sC` ASSUME_TAC THENL [C1092CPH_LIN; ALL_TAC] THEN
      C1092CPH_LIN;
      C1092CPH_FORMULA_TAC C1092WS_UPPER_NP
        (C1092CPH_SQC @ [`--sW`; `cW:real`; `--(cC * sW - sC * cW)`; `cC * cW + sC * sW`]) THEN
      C1092CPH_PROD `&0 <= (cC * sW - sC * cW) * ((&7 / &50) * cC - sC / &2 - uC - aC)` THEN
      C1092CPH_PROD `&0 <= (cC * cW + sC * sW) * (vC + aC - (&17 / &125 + sC))` THEN
      C1092CPH_PROD `&0 < (aC - &1) * (&1 + (cC * sW - sC * cW))` THEN
      MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `sW:real`] C1092CPHS_POSITIVE_OWN_MARGIN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      C1092CPH_LIN]]);;

(* Lean: nonpositive_height (private) *)
let C1092CPH_NONPOSITIVE_HEIGHT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092cpha_heightInput cC sC uC vC aC cW sW uW vW aW /\ c977cc_normal cW (--sW)
     ==> vC + aC < &17 / &125 + sC`,
  C1092CPH_SETUP_TAC C1092CPHA_NONPOSITIVE_HEIGHT_AXES C1092IFCC_NONPOSITIVE_PREDECESSOR_FACES THEN
  C1092CPH_PROD `&0 < cW * (cC - sC)` THEN C1092CPH_PROD `&0 <= sC * (cW + sW)` THEN
  C1092CPH_PROD `&0 <= sC * cW` THEN C1092CPH_PROD `&0 <= cC * (--sW)` THEN
  SUBGOAL_THEN `&0 < cC * cW + sC * sW /\ &0 <= sC * cW - cC * sW` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092CPH_LIN; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092CPH_AXES_SPLIT_TAC THENL
   [(* current *)
    C1092CPH_FORMULA_TAC C1092WS_LOWER_NP
      (C1092CPH_SQW @ [`--sC`; `cC:real`; `--(sC * cW - cC * sW)`; `cC * cW + sC * sW`]) THEN
    C1092CPH_PROD `&0 <= (sC * cW - cC * sW) * (uW + cW - sW)` THEN
    C1092CPH_PROD `&0 <= (cC * cW + sC * sW) * ((&543 / &500) * cW - aC - vW)` THEN
    C1092CPH_PROD `&0 < (aC - &1) * ((sC * cW - cC * sW) + (cC * cW + sC * sW))` THEN
    SUBGOAL_THEN `vC + aC < cC * ((&43 / &500) * cW pow 2 + c1092mifs_f cW (--sW)) +
                            sC * (c1092mifs_g cW (--sW) + (&43 / &500) * cW * sW)`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `cC * ((&43 / &500) * cW pow 2 + c1092mifs_f cW (--sW)) +
                    sC * (c1092mifs_g cW (--sW) + (&43 / &500) * cW * sW) =
                    (sC * cW - cC * sW) * (cW - sW - &1) +
                    (cC * cW + sC * sW) * ((&543 / &500) * cW - &1)` SUBST1_TAC THENL
       [REWRITE_TAC[c1092mifs_f; c1092mifs_g] THEN
        UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; C1092CPH_LIN];
      ALL_TAC] THEN
    MP_TAC(SPECL [`cW:real`; `--sW`] C1092IFCS_CAP_NEGATIVE_FG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`cW:real`; `--sW`] C1092CPHS_NEGATIVE_COEFFICIENT_UPPER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092CPH_PROD `&0 < cC * (&17 / &125 - ((&43 / &500) * cW pow 2 + c1092mifs_f cW (--sW)))` THEN
    SUBGOAL_THEN `c1092mifs_g cW (--sW) + (&43 / &500) * cW * sW =
                  cW pow 2 - (&43 / &500) * cW * --sW - cW + --sW` ASSUME_TAC THENL
     [REWRITE_TAC[c1092mifs_g] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092CPH_PROD `&0 <= sC * (&1 - (c1092mifs_g cW (--sW) + (&43 / &500) * cW * sW))` THEN
    C1092CPH_LIN;
    (* left *)
    C1092CPH_FORMULA_TAC C1092WS_UPPER_NP
      (C1092CPH_SQC @ [`--cW`; `--sW`; `--(cC * cW + sC * sW)`; `sC * cW - cC * sW`]) THEN
    SUBGOAL_THEN `uC + aC <= &7 / &50` ASSUME_TAC THENL [C1092CPH_LIN; ALL_TAC] THEN
    C1092CPH_PROD `&0 < (cC * cW + sC * sW) * (aC - (uC + aC) - &43 / &50)` THEN
    C1092CPH_PROD `&0 <= (sC * cW - cC * sW) * (vC + aC - (&17 / &125 + sC))` THEN
    C1092CPH_UNFOLD_TAC `linside cW sW uW vW aC (--(&7 / &20)) (&7 / &20)` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `--sW`] C1092CPHS_NEGATIVE_LEFT_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092CPH_LIN;
    (* right *)
    C1092CPH_FORMULA_TAC C1092TFSU_UPPER_POS_POS
      (C1092CPH_SQC @ [`--sW`; `cW:real`; `sC * cW - cC * sW`; `cC * cW + sC * sW`]) THEN
    C1092CPH_PROD `&0 <= (sC * cW - cC * sW) * (uC + aC)` THEN
    C1092CPH_PROD `&0 <= (cC * cW + sC * sW) * (vC + aC - (&17 / &125 + sC))` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `--sW`] C1092CPHS_NEGATIVE_RIGHT_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `vW < &43 / &500` ASSUME_TAC THENL [C1092CPH_LIN; ALL_TAC] THEN
    C1092CPH_LIN]);;

(* Lean: height *)
let C1092CPH_HEIGHT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aC /\ aC = aW /\ c977cc_normal cC sC /\ &99 / &100 < cC /\ sC < &7 / &50 /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     uC + aC <= (&7 / &50) * cC - sC / &2 /\
     c1092ifcc_predecessorPoints cW sW uW vW aW /\ abs sW <= cW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> vC + aC < &17 / &125 + sC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1092cpha_heightInput cC sC uC vC aC cW sW uW vW aW` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c1092cpha_heightInput]; ALL_TAC] THEN
  let vars = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
              `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] in
  ASM_CASES_TAC `&0 <= sW` THENL
   [MATCH_MP_TAC(SPECL vars C1092CPH_POSITIVE_HEIGHT);
    MATCH_MP_TAC(SPECL vars C1092CPH_NONPOSITIVE_HEIGHT)] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `abs sW <= cW` THEN REAL_ARITH_TAC);;
