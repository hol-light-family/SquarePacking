(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardSmallThreeBottom.lean          *)
(* (N12Compact.C1092MPPMInwardSmallThree; Lean header: "Source only; no      *)
(* compiler replay").  The bottom square B supplies its own transverse       *)
(* separator and its narrow signed orientation.  Squares C = cC sC uC vC aC, *)
(* B = cB sB uB vB aB (unit normals, 0 < sides explicit).  BottomProfile is  *)
(* c1092istbo_profile; BottomAngle.Input = c1092ifbd_input; lam = cC * cB +  *)
(* sC * sB, gam = --sC * cB + cC * sB.  BottomAngle lemmas: central_faces,  *)
(* separators, positive_wall, negative_wall_height, cone: C1092IFBD_*;       *)
(* angle, polynomial: C1092IFBA_*; positive_coefficients / positive_central: *)
(* C1092IFBP_*; negative_coefficients / negative_central: C1092IFBN_*;       *)
(* negative_after_margin: C1092IFBS_NEGATIVE_AFTER_MARGIN; j_bounds,         *)
(* small_bounds: C1092ISTS_*; lower_nn / lower_np: C1092WS_*; ownU: ABT_OWNU; *)
(* positive_source_margin / positive_tilt / negative_tilt: C1092ISTB_*.      *)
(* Tag C1092ISTBO_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardSmallThreeBottomScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomPositive.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomNegative.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomScalars.ml";;

(* Lean: BottomProfile (structure) *)
let c1092istbo_profile = new_definition
 `c1092istbo_profile cC sC uC vC aC cB sB uB vB (aB:real) <=>
    &999 / &1000 < cB /\ --(&43 / &1000) < sB /\ sB < &21 / &1000 /\
    &0 < cC * sB - sC * cB /\ &24 / &25 < cC * cB + sC * sB /\
    vB + aB <= --(cC * sB - sC * cB) * (uC + aC) + (cC * cB + sC * sB) * vC`;;

let C1092ISTBO_LIN = NLIN_TAC ~deg2:false [];;
let C1092ISTBO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092ISTBO_LIN; ALL_TAC];;
let C1092ISTBO_LAM = `cC * cB + sC * sB` and C1092ISTBO_GAM = `--sC * cB + cC * sB`;;
let c1092istbo_ins tm = vsubst [C1092ISTBO_LAM, `LAM:real`; C1092ISTBO_GAM, `GAM:real`] tm;;
let C1092ISTBO_CB = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;
let C1092ISTBO_CS = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
(* specialise a lemma, discharge its antecedent conjuncts from the assumptions *)
let C1092ISTBO_USE th args =
  MP_TAC(SPECL args th) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; REAL_ARITH_TAC; C1092ISTBO_LIN];
    DISCH_THEN STRIP_ASSUME_TAC];;

(* the common end of both signs (Lean: finish, local) *)
let C1092ISTBO_FINISH = prove
 (list_mk_forall(C1092ISTBO_CB, c1092istbo_ins
  `cB * cB + sB * sB = &1 /\ &0 < cB /\ &97 / &100 < cC /\ --sC < &21 / &100 /\ &0 <= --sC /\
     &0 < GAM /\ --(&43 / &1000) < sB /\ sB < &21 / &1000 /\
     vB + aB <= --GAM * (uC + aC) + LAM * vC
     ==> c1092istbo_profile cC sC uC vC aC cB sB uB vB aB`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092istbo_profile] THEN
  C1092ISTBO_PROD `&0 < (sB + &43 / &1000) * (&43 / &1000 - sB)` THEN
  SUBGOAL_THEN `&999 / &1000 < cB` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `cB - &999 / &1000`]; ALL_TAC] THEN
  C1092ISTBO_PROD `&0 < (cC - &97 / &100) * cB` THEN
  C1092ISTBO_PROD `&0 <= --sC * (&21 / &1000 - sB)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [C1092ISTBO_LIN; C1092ISTBO_LIN;
    UNDISCH_TAC (c1092istbo_ins `vB + aB <= --GAM * (uC + aC) + LAM * vC`) THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> a <= x ==> a <= y`) THEN REAL_ARITH_TAC]);;

(* Lean: bottom_profile *)
let C1092ISTBO_BOTTOM_PROFILE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ abs sB <= cB ==> c1092istbo_profile cC sC uC vC aC cB sB uB vB aB"
    C1092IFBD_VARS C1092IFBD_HYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `c1092ifbd_input a b c d e f g h i j`) (concl th) then
    MAP_EVERY ASSUME_TAC (CONJUNCTS (REWRITE_RULE[c1092ifbd_input] th)) else NO_TAC) THEN
  C1092ISTBO_USE C1092IFBD_CENTRAL_FACES C1092ISTBO_CB THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092ifbd_faces]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (can (term_match [] `a < &0 /\ b`) o concl)) THEN
  C1092PRS_NORMAL_TAC THEN
  C1092ISTBO_USE C1092IFBA_ANGLE C1092ISTBO_CB THEN
  C1092ISTBO_USE C1092IFBA_POLYNOMIAL C1092ISTBO_CB THEN
  C1092ISTBO_USE C1092ISTS_SMALL_BOUNDS [`cC:real`; `--sC`] THEN
  C1092ISTBO_USE C1092ISTS_J_BOUNDS [`cC:real`; `--sC`] THEN
  SUBGOAL_THEN `&0 < cB` ASSUME_TAC THENL
   [ASM_CASES_TAC `cB = &0` THENL
     [SUBGOAL_THEN `sB = &0` ASSUME_TAC THENL
       [UNDISCH_TAC `abs sB <= cB` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `cB * cB + sB * sB = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `~(cB = &0)` THEN UNDISCH_TAC `abs sB <= cB` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sB` THENL
   [(* positive sign *)
    SUBGOAL_THEN `c977cc_normal cB sB` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs sB <= cB` THEN UNDISCH_TAC `&0 <= sB` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092ISTBO_USE C1092IFBP_POSITIVE_COEFFICIENTS [`cC:real`; `sC:real`; `cB:real`; `sB:real`] THEN
    SUBGOAL_THEN `vB + aB <= ABT_lower cC sC uC vC aC (--sB) cB` ASSUME_TAC THENL
     [MP_TAC(SPECL C1092ISTBO_CB C1092IFBD_SEPARATORS) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
       [C1092ISTBO_USE C1092IFBP_POSITIVE_CENTRAL C1092ISTBO_CB THEN ASM_MESON_TAC[];
        C1092ISTBO_USE C1092WS_LOWER_NN (C1092ISTBO_CS @ [`cB:real`; `sB:real`; C1092ISTBO_LAM; C1092ISTBO_GAM]) THEN
        C1092ISTBO_PROD (c1092istbo_ins `&0 <= LAM * (--cC / &2 - uC)`) THEN
        C1092ISTBO_PROD (c1092istbo_ins `&0 <= GAM * (--aC - vC)`) THEN
        C1092ISTBO_PROD (c1092istbo_ins `&0 < GAM * (aC - &1)`) THEN
        C1092ISTBO_USE C1092ISTB_POSITIVE_SOURCE_MARGIN [`cC:real`; `--sC`; `cB:real`; `sB:real`] THEN
        UNDISCH_TAC `linside cB sB uB vB aB (&0) (--(&543 / &500))` THEN REWRITE_TAC[linside] THEN
        STRIP_TAC THEN C1092ISTBO_LIN;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    C1092ISTBO_USE C1092WS_LOWER_NP
      (C1092ISTBO_CS @ [`--sB`; `cB:real`; mk_comb(`(--):real->real`, C1092ISTBO_GAM); C1092ISTBO_LAM]) THEN
    C1092ISTBO_USE C1092IFBD_POSITIVE_WALL C1092ISTBO_CB THEN
    C1092ISTBO_PROD (c1092istbo_ins `&0 <= GAM * (uC - (--cC - &2 / &5 * sC))`) THEN
    C1092ISTBO_PROD (c1092istbo_ins `&0 <= LAM * (--aC - vC)`) THEN
    C1092ISTBO_PROD `&0 <= cB * (cB + sB)` THEN
    C1092ISTBO_PROD (c1092istbo_ins `&0 < (aC - &1) * (LAM + GAM + (&1 + cB * (cB + sB)) / &2)`) THEN
    SUBGOAL_THEN `cB * c1092ists_J0 cC (--sC) + (&1 - cB) pow 2 / &2 +
        sB * (cB / &2 + cC - --sC - cC pow 2 + (&2 / &5) * cC * --sC) < &0` ASSUME_TAC THENL
     [REWRITE_TAC[c1092ists_J0] THEN C1092ISTBO_LIN; ALL_TAC] THEN
    C1092ISTBO_USE C1092ISTB_POSITIVE_TILT [`cC:real`; `--sC`; `cB:real`; `sB:real`] THEN
    MATCH_MP_TAC C1092ISTBO_FINISH THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; C1092ISTBO_LIN];
    (* negative sign *)
    SUBGOAL_THEN `c977cc_normal cB (--sB)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs sB <= cB` THEN UNDISCH_TAC `~(&0 <= sB)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092PRS_NORMAL_TAC THEN
    C1092ISTBO_USE C1092IFBN_NEGATIVE_COEFFICIENTS [`cC:real`; `sC:real`; `cB:real`; `sB:real`] THEN
    C1092ISTBO_USE C1092IFBD_NEGATIVE_WALL_HEIGHT C1092ISTBO_CB THEN
    SUBGOAL_THEN `vB + aB <= ABT_lower cC sC uC vC aC (--sB) cB` ASSUME_TAC THENL
     [MP_TAC(SPECL C1092ISTBO_CB C1092IFBD_SEPARATORS) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
       [C1092ISTBO_USE C1092IFBN_NEGATIVE_CENTRAL C1092ISTBO_CB THEN ASM_MESON_TAC[];
        MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNU) THEN
        ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        MP_TAC(SPECL (C1092ISTBO_CB @ [`cB:real`; `sB:real`]) C1092IFBD_CONE) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
           [REWRITE_TAC[REAL_POW_2] THEN FIRST_ASSUM ACCEPT_TAC;
            FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th = `ABT_upper cB sB uB vB aB cB sB = uB + aB`)) THEN
            FIRST_ASSUM ACCEPT_TAC];
          STRIP_TAC THEN UNDISCH_TAC `~(&0 <= sB)` THEN UNDISCH_TAC `&0 < sB` THEN REAL_ARITH_TAC];
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN (c1092istbo_ins `&0 < GAM`) ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092ISTBO_USE C1092WS_LOWER_NN
        (C1092ISTBO_CS @ [`--sB`; `cB:real`; mk_comb(`(--):real->real`, C1092ISTBO_GAM); C1092ISTBO_LAM]) THEN
      C1092ISTBO_PROD (c1092istbo_ins `&0 <= --GAM * (--cC / &2 - uC)`) THEN
      C1092ISTBO_PROD (c1092istbo_ins `&0 <= LAM * (--aC - vC)`) THEN
      C1092ISTBO_PROD (c1092istbo_ins `&0 < LAM * (aC - &1)`) THEN
      C1092ISTBO_USE C1092IFBS_NEGATIVE_AFTER_MARGIN [`cC:real`; `--sC`; `cB:real`; `--sB`] THEN
      C1092ISTBO_LIN;
      ALL_TAC] THEN
    C1092ISTBO_USE C1092WS_LOWER_NP
      (C1092ISTBO_CS @ [`--sB`; `cB:real`; mk_comb(`(--):real->real`, C1092ISTBO_GAM); C1092ISTBO_LAM]) THEN
    C1092ISTBO_PROD (c1092istbo_ins `&0 <= GAM * (uC - (--cC - &2 / &5 * sC))`) THEN
    C1092ISTBO_PROD (c1092istbo_ins `&0 <= LAM * (--aC - vC)`) THEN
    C1092ISTBO_PROD (c1092istbo_ins `&0 < (aC - &1) * (GAM + LAM)`) THEN
    SUBGOAL_THEN (c1092istbo_ins `LAM + c1092ists_Q cC (--sC) * GAM < &1`) ASSUME_TAC THENL
     [REWRITE_TAC[c1092ists_Q] THEN C1092ISTBO_LIN; ALL_TAC] THEN
    C1092ISTBO_USE C1092ISTB_NEGATIVE_TILT [`cC:real`; `--sC`; `cB:real`; `--sB`] THEN
    MATCH_MP_TAC C1092ISTBO_FINISH THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; C1092ISTBO_LIN]]);;
