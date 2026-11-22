(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalAngle.lean                *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  The full predecessor normal *)
(* join of CENTERED-NEGATIVE-INWARD-ANGLE.  Squares C, W, B, K are           *)
(* cC sC uC vC aC, cW .., cB .., cK ..; CenteredCapInput: c1092ifh_capInput  *)
(* (CP_C1092_MPPMInwardFinalHeight.ml, with reject_first / positive_axes /   *)
(* centered_height_cap = C1092IFH_ names).  angle rows / angleFz .. angleGl:      *)
(* C1092IFAR_* / c1092ifar_*; angle_endpoint / angle_own_positive /          *)
(* angle_left / angle_right_before: C1092IFAS_*; relative_order:             *)
(* C1092MIFS_RELATIVE_ORDER; coordinates_after: C1092MIFSS_COORDINATES_AFTER;*)
(* half_cross: C1092MIFE_HALF_CROSS; CanonicalProjection.before: CCCP_BEFORE;*)
(* BottomCorner / bottom_origin: c1092ifc_bottomCorner / C1092IFC_BOTTOM_ORIGIN*)
(* ; OriginalOwners.vertical_segment: OO_VERTICAL_SEGMENT; the remaining     *)
(* names as in CP_C1092_MPPMInwardFinalHeight.ml.  Tag C1092IFA_.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalAngleRows.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalHeight.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCentered.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessorScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalEndpoints.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

let C1092IFA_LIN = C1092IFH_LIN;;
let C1092IFA_PROD = C1092IFH_PROD;;

(* Lean: positive_angle (private) *)
let C1092IFA_POSITIVE_ANGLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\ c977cc_normal cW sW
     ==> C1092WPS_half cC (--sC) < &21 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFH_POSITIVE_AXES) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C1092IFCC_NONNEGATIVE_PREDECESSOR_FACES) THEN
  UNDISCH_TAC `c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW` THEN
  REWRITE_TAC[c1092ifh_capInput] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_TAC THEN
  C1092IFH_PRED_TAC THEN C1092IFH_NORMAL_TAC THEN
  C1092IFA_PROD `&0 <= (cC + sC) * cW` THEN
  C1092IFA_PROD `&0 <= (--sC) * (cW - sW)` THEN
  C1092IFA_PROD `&0 <= cC * sW` THEN
  C1092IFA_PROD `&0 <= (--sC) * cW` THEN
  SUBGOAL_THEN `&0 <= cC * cW + sC * sW /\ &0 <= cC * sW - sC * cW` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092IFA_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < vC + aC` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFAS_ANGLE_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `ABT_upper`)) (concl th))) THENL
   [(* own *)
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC`; `cC:real`;
                  `cC * sW - sC * cW`; `cC * cW + sC * sW`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REAL_ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
      is_disj(concl th) && not (can (find_term ((=) `ABT_upper`)) (concl th)))) THENL
     [(* topV *)
      SUBGOAL_THEN `uW < (&7 / &20) * (sW - cW)` ASSUME_TAC THENL
       [UNDISCH_TAC `linside cW sW uW vW aC (--(&7 / &20)) (&7 / &20)` THEN
        REWRITE_TAC[linside] THEN STRIP_TAC THEN C1092IFA_LIN; ALL_TAC] THEN
      C1092IFA_PROD `&0 <= (cC * sW - sC * cW) * ((&7 / &20) * (sW - cW) - uW)` THEN
      C1092IFA_PROD `&0 <= (cC * cW + sC * sW) * ((&543 / &500) * cW - &1 - vW)` THEN
      MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `sW:real`] C1092IFAR_ANGLE_Z_ROW) THEN
      ASM_REWRITE_TAC[c1092ifar_angleFz; c1092ifar_angleGz] THEN DISCH_TAC THEN
      C1092IFA_LIN;
      (* topU *)
      FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC o check (fun th ->
        is_conj(concl th) && is_disj(rand(concl th)))) THEN
      C1092IFA_PROD `&0 <= (cC * sW - sC * cW) * ((&543 / &500) * sW - &1 - uW)` THENL
       [C1092IFA_PROD `&0 <= (cC * cW + sC * sW) * (cW + sW - &1 - vW)` THEN
        SUBGOAL_THEN `vC + aC <= cC * ((cW + sW - &1) pow 2 / &2 + (&43 / &500) * sW pow 2) +
                                 sC * (sW pow 2 + cW - sW - (&43 / &500) * cW * sW)`
          ASSUME_TAC THENL
         [SUBGOAL_THEN `cC * ((cW + sW - &1) pow 2 / &2 + (&43 / &500) * sW pow 2) +
                        sC * (sW pow 2 + cW - sW - (&43 / &500) * cW * sW) =
                        (cC * sW - sC * cW) * ((&543 / &500) * sW - &1) +
                        (cC * cW + sC * sW) * (cW + sW - &1)` SUBST1_TAC THENL
           [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; C1092IFA_LIN];
          ALL_TAC] THEN
        MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `sW:real`] C1092IFAR_ANGLE_F0_ROW) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092IFA_LIN;
        C1092IFA_PROD `&0 <= (cC * cW + sC * sW) * ((&543 / &500) * cW + sW - &1 - vW)` THEN
        SUBGOAL_THEN `vC + aC <= cC * (&43 / &500 + (cW + sW - &1) pow 2 / &2) +
                                 sC * (sW pow 2 + cW - sW)` ASSUME_TAC THENL
         [SUBGOAL_THEN `cC * (&43 / &500 + (cW + sW - &1) pow 2 / &2) + sC * (sW pow 2 + cW - sW) =
                        (cC * sW - sC * cW) * ((&543 / &500) * sW - &1) +
                        (cC * cW + sC * sW) * ((&543 / &500) * cW + sW - &1)` SUBST1_TAC THENL
           [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; C1092IFA_LIN];
          ALL_TAC] THEN
        MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `sW:real`] C1092IFAR_ANGLE_G0_ROW) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092IFA_LIN]];
    (* last *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
                  `--(cC * sW - sC * cW)`; `cC * cW + sC * sW`] C1092WS_UPPER_NP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFA_LIN;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    C1092IFA_PROD `&0 <= (cC * sW - sC * cW) * ((&7 / &50) * cC - sC / &2 - uC - aC)` THEN
    C1092IFA_PROD `&0 <= (cC * cW + sC * sW) * (vC + aC)` THEN
    C1092IFA_PROD `&0 < (aC - &1) * (&1 + (cC * sW - sC * cW))` THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `sW:real`] C1092IFAS_ANGLE_OWN_POSITIVE) THEN
    ASM_REWRITE_TAC[c1092ifcs_centeredD] THEN DISCH_TAC THEN
    C1092IFA_LIN]);;

(* Lean: nonpositive_angle (private) *)
let C1092IFA_NONPOSITIVE_ANGLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\ c977cc_normal cW (--sW)
     ==> C1092WPS_half cC (--sC) < &21 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFH_REJECT_FIRST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C1092IFCC_NONPOSITIVE_PREDECESSOR_FACES) THEN
  UNDISCH_TAC `c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW` THEN
  REWRITE_TAC[c1092ifh_capInput] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092IFH_PRED_TAC THEN C1092IFH_NORMAL_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] C1092MIFP_UPWARD_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092IFA_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092UTS_RELATIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cC * cW + sC * sW` ASSUME_TAC THENL [C1092IFA_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < uC + aC /\ &0 < --uC /\ &0 < vC + aC /\ &0 < --vC` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFAS_ANGLE_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `ABT_upper`)) (concl th))) THENL
   [(* first: excluded by reject_first when the disjunction was rewritten *)
    (* own *)
    ASM_CASES_TAC `sC * cW - cC * sW <= &0` THENL
     [MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC`; `cC:real`;
                    `--(sC * cW - cC * sW)`; `cC * cW + sC * sW`] C1092WS_LOWER_NN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFA_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      SUBGOAL_THEN `uW < --(&7 / &20) * (cW - sW)` ASSUME_TAC THENL
       [UNDISCH_TAC `linside cW sW uW vW aC (--(&7 / &20)) (&7 / &20)` THEN
        REWRITE_TAC[linside] THEN STRIP_TAC THEN C1092IFA_LIN; ALL_TAC] THEN
      C1092IFA_PROD `&0 <= (--(sC * cW - cC * sW)) * (--(&7 / &20) * (cW - sW) - uW)` THEN
      C1092IFA_PROD `&0 <= (cC * cW + sC * sW) * ((&543 / &500) * cW - &1 - vW)` THEN
      MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092IFAR_ANGLE_LEFT_ROW) THEN
      ASM_REWRITE_TAC[c1092ifar_angleFl; c1092ifar_angleGl] THEN DISCH_TAC THEN
      C1092IFA_LIN;
      MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC`; `cC:real`;
                    `--(sC * cW - cC * sW)`; `cC * cW + sC * sW`] C1092WS_LOWER_NP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFA_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFA_PROD `&0 <= (sC * cW - cC * sW) * (uW + cW - sW)` THEN
      C1092IFA_PROD `&0 <= (cC * cW + sC * sW) * ((&543 / &500) * cW - aC - vW)` THEN
      C1092IFA_PROD `&0 < (aC - &1) * ((sC * cW - cC * sW) + (cC * cW + sC * sW))` THEN
      SUBGOAL_THEN `vC + aC < cC * ((&43 / &500) * cW pow 2 + c1092mifs_f cW (--sW)) +
                              sC * (c1092mifs_g cW (--sW) + (&43 / &500) * cW * sW)`
        ASSUME_TAC THENL
       [SUBGOAL_THEN `cC * ((&43 / &500) * cW pow 2 + c1092mifs_f cW (--sW)) +
                      sC * (c1092mifs_g cW (--sW) + (&43 / &500) * cW * sW) =
                      (sC * cW - cC * sW) * (cW - sW - &1) +
                      (cC * cW + sC * sW) * ((&543 / &500) * cW - &1)` SUBST1_TAC THENL
         [REWRITE_TAC[c1092mifs_f; c1092mifs_g] THEN
          UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; C1092IFA_LIN];
        ALL_TAC] THEN
      SUBGOAL_THEN `&21 / &100 <= C1092WPS_half cW (--sW)` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        MP_TAC(SPECL [`cW:real`; `--sW`; `cC:real`; `--sC`] C1092MIFS_RELATIVE_ORDER) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFA_LIN; DISCH_TAC] THEN
        C1092IFA_LIN;
        ALL_TAC] THEN
      MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092IFAR_ANGLE_RIGHT_ROW) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      C1092IFA_LIN];
    (* wu *)
    C1092IFA_PROD `&0 <= (cC * cW + sC * sW) * ((&7 / &50) * cC - sC / &2 - uC - aC)` THEN
    C1092IFA_PROD `&0 < (aC - &1) * (&1 + (cC * cW + sC * sW))` THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092IFAS_ANGLE_LEFT) THEN
    ASM_REWRITE_TAC[c1092ifcs_centeredD] THEN DISCH_TAC THEN
    ASM_CASES_TAC `&0 <= sC * cW - cC * sW` THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--cW`; `--sW`;
                    `--(cC * cW + sC * sW)`; `sC * cW - cC * sW`] C1092WS_UPPER_NP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFA_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFA_PROD `&0 <= (sC * cW - cC * sW) * (vC + aC)` THEN
      C1092IFA_LIN;
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--cW`; `--sW`;
                    `--(cC * cW + sC * sW)`; `sC * cW - cC * sW`] C1092TFSU_UPPER_NEG_NEG) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFA_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFA_PROD `&0 <= (--(sC * cW - cC * sW)) * (--vC)` THEN
      C1092IFA_LIN];
    (* wv *)
    ASM_CASES_TAC `&0 <= sC * cW - cC * sW` THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
                    `sC * cW - cC * sW`; `cC * cW + sC * sW`] C1092TFSU_UPPER_POS_POS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFA_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFA_PROD `&0 <= (sC * cW - cC * sW) * (uC + aC)` THEN
      C1092IFA_PROD `&0 < (cC * cW + sC * sW) * (vC + aC)` THEN
      MP_TAC(SPECL [`cW:real`; `--sW`; `cC:real`; `--sC`] C1092MIFSS_COORDINATES_AFTER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFA_LIN; STRIP_TAC] THEN
      C1092IFA_LIN;
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
                    `sC * cW - cC * sW`; `cC * cW + sC * sW`] C1092WS_UPPER_NP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFA_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFA_PROD `&0 <= (--(sC * cW - cC * sW)) * ((&7 / &50) * cC - sC / &2 - uC - aC)` THEN
      C1092IFA_PROD `&0 <= (cC * cW + sC * sW) * (vC + aC)` THEN
      C1092IFA_PROD `&0 < (aC - &1) * (&1 - (sC * cW - cC * sW))` THEN
      MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092IFAS_ANGLE_RIGHT_BEFORE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFA_LIN; ALL_TAC] THEN
      REWRITE_TAC[c1092ifcs_centeredD] THEN DISCH_TAC THEN
      C1092IFA_LIN]]);;

(* Lean: centered_half_angle *)
let C1092IFA_CENTERED_HALF_ANGLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\ abs sW <= cW
     ==> C1092WPS_half cC (--sC) < &21 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let vars = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
              `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] in
  ASM_CASES_TAC `&0 <= sW` THENL
   [MATCH_MP_TAC(SPECL vars C1092IFA_POSITIVE_ANGLE);
    MATCH_MP_TAC(SPECL vars C1092IFA_NONPOSITIVE_ANGLE)] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `abs sW <= cW` THEN REAL_ARITH_TAC);;

(* Lean: centered_outer_halfpoint *)
let C1092IFA_CENTERED_OUTER_HALFPOINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c (--s) /\ s < &0 /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
     v + a < &17 / &125 /\ C1092WPS_half c (--s) < &21 / &100 /\
     (linside c s u v a (--(&1)) (--(&13 / &50)) \/ linside c s u v a (--(&1)) (--(&2 / &5)))
     ==> linside c s u v a (--(&1)) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c (--s)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal c (--s)`)) THEN
  SUBGOAL_THEN `c977cc_normal (&9559 / &10441) (&4200 / &10441)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half (&9559 / &10441) (&4200 / &10441) = &21 / &100` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s`; `&9559 / &10441`; `&4200 / &10441`] C1092MIFE_HALF_CROSS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s`; `&9559 / &10441`; `&4200 / &10441`; `&1 / &2`; `&1`] CCCP_BEFORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN C1092IFA_LIN; DISCH_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN
  REPEAT STRIP_TAC THEN C1092IFA_LIN);;

(* Lean: centered_outer_consequences *)
let C1092IFA_CENTERED_OUTER_CONSEQUENCES = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\ abs sW <= cW /\ sC < &0 /\
     ~(linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
       linside cC sC uC vC aC (--(&1)) (--(&2 / &5)))
     ==> ~linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
         (linside cC sC uC vC aC (--(&1)) (--(&2 / &5))
          ==> linside cC sC uC vC aC (--(&1)) (--(&1 / &2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFH_CENTERED_HEIGHT_CAP) THEN
  MP_TAC(SPEC_ALL C1092IFA_CENTERED_HALF_ANGLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifh_capInput] o
    check (fun th -> can (term_match [] `c1092ifh_capInput a b c d e f g h i j`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  let half = SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
                   C1092IFA_CENTERED_OUTER_HALFPOINT in
  CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC half THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
                   linside cC sC uC vC aC (--(&1)) (--(&2 / &5)))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`--(&1 / &2)`; `--(&13 / &50)`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_TAC THEN MP_TAC half THEN ASM_REWRITE_TAC[]]);;

(* Lean: centered_outer_origin *)
let C1092IFA_CENTERED_OUTER_ORIGIN = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cB sB uB vB aB cK sK uK vK aK.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\ abs sW <= cW /\ sC < &0 /\
     ~(linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
       linside cC sC uC vC aC (--(&1)) (--(&2 / &5))) /\
     linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\
     c1092ifc_bottomCorner cB sB uB vB aB cK sK uK vK aK /\
     ldisj cC sC uC vC aC cK sK uK vK aK
     ==> linside cB sB uB vB aB (&0) (--(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                      `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                      `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] C1092IFC_BOTTOM_ORIGIN) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C1092IFA_CENTERED_OUTER_CONSEQUENCES) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
