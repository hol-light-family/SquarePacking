(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositivePredecessor.lean       *)
(* (N12Compact.C1092MPPMAllNonpositive), ALL-NEGATIVE-MIXED-FORWARD-ENDING  *)
(* sections 5.1-5.2.  Squares C = cC sC uC vC aC and W = cW sW uW vW aW with *)
(* their OpenSquare invariants as hypotheses.  Core / faces: c1092anc_core / *)
(* C1092ANC_FACES; MissingPredecessor c1092manp_missingPredecessor;          *)
(* AlternatingScalars sine_small / missing_bounds / predecessorF / G /       *)
(* predecessor_coefficients: C1092ANAS_*; dot_le_one C977CSB_DOT_LE_ONE;     *)
(* faceSeparation_of_disjoint CSAT_FACESEPARATION_OF_DISJOINT; separated /   *)
(* parallel_radius / transverse_radius / strict_bounds / ownV / lower /      *)
(* upper: ABT_*; lower_nn / lower_np / upper_np C1092WS_*; upper_nn          *)
(* C1092MEA_UPPER_NN.  With c = cC, s = --sC, b = cW, r = --sW the Lean lets *)
(* are k = cC * cW + sC * sW and z = --cC * sW + sC * cW.  Tag C1092MANPR_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositiveProfiles.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveAlternatingScalars.ml";;
needs "n12/geometry/CongruentSAT.ml";;

let C1092MANPR_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;
let C1092MANPR_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MANPR_LP_TAC; ALL_TAC];;
let C1092MANPR_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092MANPR_LP_TAC; ALL_TAC];;

(* one separating-axis case of vertical_axes; C = (cC,sC,uC,vC), W = (cW,sW,uW,vW), side aC *)
let C1092MANPR_CASE_TAC nx ny swap radius points =
  let sep = SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                   `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; nx; ny]
                  ABT_SEPARATED in
  let sb ((c,s,u,v),(x,y)) =
    MP_TAC(SPECL [c; s; u; v; `aC:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     ASM_REAL_ARITH_TAC; STRIP_TAC] in
  MP_TAC sep THEN ANTS_TAC THENL
  [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
    else ALL_TAC) THEN
   MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY sb points THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; RASM_ARITH_TAC];;

(* Lean: vertical_axes (private) *)
let C1092MANPR_VERTICAL_AXES = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092anc_core cC sC uC vC aC /\ c977cc_normal cW (--sW) /\ aC = aW /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> vC + aC <= ABT_lower cW sW uW vW aW (--sC) cC \/
         ABT_upper cC sC uC vC aC (--sW) cW <= vW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o check (c1092mpapo_head `c1092anc_core`)) THEN
  MAP_EVERY (fun (c, s) -> c1092mabo_normal_tac c s) [`cC:real`, `--sC`; `cW:real`, `--sW`] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let qC = (`cC:real`,`sC:real`,`uC:real`,`vC:real`)
  and qW = (`cW:real`,`sW:real`,`uW:real`,`vW:real`) in
  let pts = [(qC,(`--(&7 / &20)`,`--(&7 / &20)`)); (qW,(`--(&7 / &20)`,`&7 / &20`));
             (qC,(`--(&1)`,`--(&13 / &50)`))] in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [C1092MANPR_CASE_TAC `cC:real` `sC:real` false
     (SPECL [`cC:real`; `sC:real`; `aC:real`; `cW:real`; `sW:real`; `aC:real`] ABT_PARALLEL_RADIUS) pts;
   C1092MANPR_CASE_TAC `--sC:real` `cC:real` false
     (SPECL [`cC:real`; `sC:real`; `aC:real`; `cW:real`; `sW:real`; `aC:real`] ABT_TRANSVERSE_RADIUS) pts;
   C1092MANPR_CASE_TAC `cW:real` `sW:real` true
     (SPECL [`cW:real`; `sW:real`; `aC:real`; `cC:real`; `sC:real`; `aC:real`] ABT_PARALLEL_RADIUS) pts;
   C1092MANPR_CASE_TAC `--sW:real` `cW:real` true
     (SPECL [`cW:real`; `sW:real`; `aC:real`; `cC:real`; `sC:real`; `aC:real`] ABT_TRANSVERSE_RADIUS) pts]);;

(* Lean: predecessor_cap *)
let C1092MANPR_PREDECESSOR_CAP = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092anc_core cC sC uC vC aC /\ c1092manp_missingPredecessor cW sW uW vW aW /\ aC = aW /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> vC + aC < (&43 / &500) * cC + (&12 / &25) * sC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C1092MANPR_VERTICAL_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[c1092manp_missingPredecessor] o
      check (c1092mpapo_head `c1092manp_missingPredecessor`));
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o check (c1092mpapo_head `c1092anc_core`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092manp_missingPredecessor] o
    check (c1092mpapo_head `c1092manp_missingPredecessor`)) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092ANAS_SINE_SMALL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cW:real`; `--sW`] C1092ANAS_MISSING_BOUNDS) THEN
  ASM_REWRITE_TAC[c1092anas_missingBounds] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `--sW`] C1092ANAS_PREDECESSOR_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[c1092anas_predecessorF; c1092anas_predecessorG; REAL_POW_2] THEN STRIP_TAC THEN
  MAP_EVERY (fun (c, s) -> c1092mabo_normal_tac c s) [`cC:real`, `--sC`; `cW:real`, `--sW`] THEN
  MAP_EVERY (fun tm -> FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[linside] o check (fun th -> concl th = tm)) THEN
                       STRIP_TAC)
    [`linside cC sC uC vC aC (--(&1)) (--(&13 / &50))`; `linside cC sC uC vC aC (--(&13 / &50)) (&0)`] THEN
  C1092MANPR_FACT `&0 < cC /\ &0 < cW /\ &0 < --sC /\ &0 <= --sW` THEN
  C1092MANPR_PROD `&0 < cC * cW` THEN C1092MANPR_PROD `&0 <= --sC * --sW` THEN
  C1092MANPR_FACT `&0 < cC * cW + sC * sW` THEN
  C1092MANPR_FACT `&0 < uC + aC /\ uC < &0 /\ (&13 / &50) * sC < vC + aC /\ vW < --(&131 / &500)` THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [(* current *)
    SUBGOAL_THEN `&0 < --cC * sW + sC * cW` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC`; `cC:real`;
        `--(--cC * sW + sC * cW)`; `cC * cW + sC * sW`] C1092WS_LOWER_NN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MANPR_LP_TAC; DISCH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `ABT_lower`)) (concl th) && not (is_eq (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      C1092MANPR_FACT `uW < &0` THEN
      C1092MANPR_PROD `&0 <= --(--cC * sW + sC * cW) * --uW` THEN
      C1092MANPR_PROD `&0 <= (cC - --sC) * --sW` THEN
      C1092MANPR_PROD `&0 <= (&71 / &100 - --sC) * (cW - --sW)` THEN
      C1092MANPR_FACT `--(&1 / &20) < --cC * sW + sC * cW` THEN
      SUBGOAL_THEN `(cC * cW + sC * sW) pow 2 + (--cC * sW + sC * cW) pow 2 = &1` ASSUME_TAC THENL
       [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
        CONV_TAC REAL_RING; ALL_TAC] THEN
      C1092MANPR_PROD `&0 < ((--cC * sW + sC * cW) + &1 / &20) * (&1 / &20 - (--cC * sW + sC * cW))` THEN
      SUBGOAL_THEN `&99 / &100 < cC * cW + sC * sW` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
        C1092MANPR_PROD `&0 <= (&99 / &100 - (cC * cW + sC * sW)) * (&99 / &100 + (cC * cW + sC * sW))` THEN
        RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MANPR_LP_TAC;
        ALL_TAC] THEN
      C1092MANPR_PROD `&0 < (cC * cW + sC * sW) * (--(&131 / &500) - vW)` THEN
      C1092MANPR_LP_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC`; `cC:real`;
      `--(--cC * sW + sC * cW)`; `cC * cW + sC * sW`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MANPR_LP_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `ABT_lower`)) (concl th) && not (is_eq (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092MANPR_PROD `&0 <= (--cC * sW + sC * cW) * ((uW + aC) - (aC - cW - --sW))` THEN
    C1092MANPR_PROD `&0 <= (cC * cW + sC * sW) * ((cW - aC) - vW)` THEN
    C1092MANPR_PROD `&0 < (aC - &1) * ((cC * cW + sC * sW) + (--cC * sW + sC * cW))` THEN
    SUBGOAL_THEN `--(--cC * sW + sC * cW) * (&1 - cW - --sW) + (cC * cW + sC * sW) * (cW - &1) =
                  cC * (&1 + cW * --sW - cW - --sW) - --sC * (cW * cW - cW + --sW)` ASSUME_TAC THENL
     [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MANPR_PROD `&0 < cC * (&43 / &500 - (&1 + cW * --sW - cW - --sW))` THEN
    C1092MANPR_PROD `&0 <= --sC * ((cW * cW - cW + --sW) - &12 / &25)` THEN
    C1092MANPR_LP_TAC;
    (* foreign *)
    C1092MANPR_PROD `&0 < (cC * cW + sC * sW) * ((vC + aC) - (&13 / &50) * sC)` THEN
    SUBGOAL_THEN `--(&13 / &50) * (cC * cW + sC * sW) * --sC < ABT_upper cC sC uC vC aC (--sW) cW`
      ASSUME_TAC THENL
     [ASM_CASES_TAC `&0 <= --cC * sW + sC * cW` THENL
       [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
          `--cC * sW + sC * cW`; `cC * cW + sC * sW`] C1092MEA_UPPER_NN) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MANPR_LP_TAC; DISCH_THEN SUBST1_TAC] THEN
        C1092MANPR_PROD `&0 <= (--cC * sW + sC * cW) * (uC + aC)` THEN C1092MANPR_LP_TAC;
        MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
          `--cC * sW + sC * cW`; `cC * cW + sC * sW`] C1092WS_UPPER_NP) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MANPR_LP_TAC; DISCH_THEN SUBST1_TAC] THEN
        C1092MANPR_PROD `&0 <= --(--cC * sW + sC * cW) * --uC` THEN C1092MANPR_LP_TAC];
      ALL_TAC] THEN
    C1092MANPR_PROD `&0 <= --sC * (&1 - (cC * cW + sC * sW))` THEN
    C1092MANPR_LP_TAC]);;
