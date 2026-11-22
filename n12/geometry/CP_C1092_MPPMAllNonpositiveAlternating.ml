(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositiveAlternating.lean       *)
(* (N12Compact.C1092MPPMAllNonpositive), ALL-NEGATIVE-MIXED-FORWARD-ENDING  *)
(* section 6.  Squares C, W, E and the bar owner B are (cC, ..), (cW, ..),  *)
(* (cE, ..), (cB, ..) with their OpenSquare invariants as hypotheses.       *)
(* Core / faces c1092anc_core / C1092ANC_FACES; MissingPredecessor /        *)
(* MissingSuccessor c1092manp_*; predecessor_shallow / Shallow              *)
(* C1092ANSH_PREDECESSOR_SHALLOW / c1092ansh_shallow; missing_bounds        *)
(* C1092ANAS_MISSING_BOUNDS; OrdinaryNegativeHalfpoint Frame / axes         *)
(* c1092onh_frame / C1092ONHF_AXES; lower_nn / formulas C1092WS_*;          *)
(* OnePositive.missing_negative_longitudinal                                *)
(* C1092OPS_MISSING_NEGATIVE_LONGITUDINAL.  With c = cC, s = --sC, d = cE,  *)
(* t = --sE, the Lean lets k, z are cC * cE + sC * sE and                    *)
(* cC * --sE + sC * cE.  Tag C1092ANAL_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositiveShallow.ml";;
needs "n12/geometry/CP_C1092_MPPMOnePositiveScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryNegativeHalfpointFaces.ml";;

let C1092ANAL_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;
let C1092ANAL_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092ANAL_LP_TAC; ALL_TAC];;
let C1092ANAL_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092ANAL_LP_TAC; ALL_TAC];;

(* Lean: alternating_impossible *)
let C1092ANAL_ALTERNATING_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092anc_core cC sC uC vC aC /\
     c1092manp_missingPredecessor cW sW uW vW aW /\ c1092manp_missingSuccessor cE sE uE vE aE /\
     aC = aW /\ aC = aE /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     ldisj cC sC uC vC aC cW sW uW vW aW /\
     ldisj cC sC uC vC aC cE sE uE vE aE /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092ANSH_PREDECESSOR_SHALLOW) THEN
  ASM_REWRITE_TAC[c1092ansh_shallow] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o check (c1092mpapo_head `c1092anc_core`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092manp_missingSuccessor] o
    check (c1092mpapo_head `c1092manp_missingSuccessor`)) THEN
  MAP_EVERY (fun tm -> STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (ASSUME tm)) THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] (ASSUME tm)))
    [`c977cc_normal cC (--sC)`; `c977cc_normal cE (--sE)`] THEN
  MP_TAC(SPECL [`cE:real`; `--sE`] C1092ANAS_MISSING_BOUNDS) THEN
  ASM_REWRITE_TAC[c1092anas_missingBounds] THEN STRIP_TAC THEN
  C1092ANAL_FACT `&0 < cC /\ &0 < cE` THEN
  C1092ANAL_PROD `&0 < cC * cE` THEN C1092ANAL_PROD `&0 <= --sC * --sE` THEN
  C1092ANAL_FACT `&0 < cC * cE + sC * sE` THEN
  C1092ANAL_PROD `&0 <= cC * (--sE - &27 / &40)` THEN
  C1092ANAL_PROD `&0 <= cE * (cC / &4 - --sC)` THEN
  C1092ANAL_PROD `&0 <= cC * (&369 / &500 - cE)` THEN
  C1092ANAL_FACT `&19 / &40 < cC * --sE + sC * cE` THEN
  C1092ANAL_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) + (cC * --sE + sC * cE))` THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092ONHF_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092onh_frame; REAL_POW_2] THEN C1092ANAL_LP_TAC; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [(* current *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
      `cC * cE + sC * sE`; `cC * --sE + sC * cE`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092ANAL_LP_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    C1092ANAL_PROD `&0 <= (cC * cE + sC * sE) * ((cE + --sE - aC) - uE)` THEN
    C1092ANAL_PROD `&0 <= (cC * --sE + sC * cE) * ((--sE - (&14 / &25) * cE - aC) - vE)` THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092OPS_MISSING_NEGATIVE_LONGITUDINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092ANAL_LP_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&1 - cC + (cC * cE + sC * sE) * (&1 - cE - --sE) +
                  (cC * --sE + sC * cE) * (&1 - --sE + (&14 / &25) * cE) =
                  &1 - (&2 - cE - --sE + (&11 / &25) * cE * --sE) * cC -
                  (&1 + cE - --sE - (&11 / &25) * cE pow 2) * --sC` ASSUME_TAC THENL
     [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    C1092ANAL_LP_TAC;
    (* recipient *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`]
      C1092WS_FORMULAS) THEN
    SUBGOAL_THEN `&0 <= cE * cC + sE * sC /\ --cE * sC + sE * cC <= &0` STRIP_ASSUME_TAC THENL
     [C1092ANAL_LP_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`; REAL_ARITH `x <= &0 ==> max x (&0) = &0`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      can (find_term ((=) `ABT_upper`)) (lhs (concl th)))) THEN
    C1092ANAL_PROD `&0 <= (cC * cE + sC * sE) * ((uC + aC) - (aC - cC))` THEN
    C1092ANAL_PROD `&0 < (cC * --sE + sC * cE) * (&43 / &500 - (vC + aC))` THEN
    C1092ANAL_PROD `&0 <= (cC * cE + sC * sE) * (&1 - cC)` THEN
    C1092ANAL_LP_TAC]);;
