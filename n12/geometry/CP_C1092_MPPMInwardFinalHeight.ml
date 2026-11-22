(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalHeight.lean               *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  The actual predecessor      *)
(* normal joins in CENTERED-NEGATIVE-INWARD-H-CAP.  Squares C, E, W are      *)
(* cC sC uC vC aC, cE sE uE vE aE, cW sW uW vW aW.  Normal: c977cc_normal;   *)
(* normal_bounds: C977CC_NORMAL_BOUNDS; PredecessorPoints:                   *)
(* c1092ifcc_predecessorPoints; NegativeSuccessor: c1092ifsu_negsucc;        *)
(* lower / upper: ABT_lower / ABT_upper; strict_bounds / ownU / ownV:        *)
(* ABT_STRICT_BOUNDS / ABT_OWNU / ABT_OWNV; faceSeparation_of_disjoint with  *)
(* separated / parallel_radius / transverse_radius: ABT_FOUR_AXES; reverse:  *)
(* C1092TFSU_REVERSE; upper_neg / lower_neg: C1092TFSU_UPPER_NEG / _LOWER_NEG;*)
(* lower_nn / lower_np / upper_np: C1092WS_*; upper_pos_pos / upper_neg_neg: *)
(* C1092TFSU_*; upward_axes: C1092MIFP_UPWARD_AXES; cap scalars: C1092IFCS_* *)
(* (centeredD: c1092ifcs_centeredD); f, g: c1092mifs_f, c1092mifs_g;         *)
(* relative_bounds: C1092UTS_RELATIVE_BOUNDS; predecessor faces / marker and *)
(* first caps: C1092IFCC_*.  Structure CenteredCapInput:                     *)
(* c1092ifh_capInput (the OpenSquare unit normals / positive sides are       *)
(* explicit hypotheses).  Tag C1092IFH_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCapScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalPredecessor.ml";;
needs "n12/geometry/CP_C1092_MMMP_UpperThirdScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCenteredCaps.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;

let C1092IFH_LIN = NLIN_TAC ~deg2:false [];;

let C1092IFH_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC THEN
   C1092IFH_LIN; ALL_TAC];;

let C1092IFH_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: CenteredCapInput (structure) *)
let c1092ifh_capInput = new_definition
 `c1092ifh_capInput (cC:real) (sC:real) (uC:real) (vC:real) (aC:real)
                    (cW:real) (sW:real) (uW:real) (vW:real) (aW:real) <=>
    &1 < aC /\
    aC = aW /\
    c977cc_normal cC (--sC) /\
    linside cC sC uC vC aC (&0) (&0) /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    uC + aC <= (&7 / &20) * (cC - sC) /\
    vC + aC <= (&7 / &20) * (cC + sC) /\
    uC + aC <= (&7 / &50) * cC - sC / &2 /\
    c1092ifcc_predecessorPoints cW sW uW vW aW /\
    ldisj cC sC uC vC aC cW sW uW vW aW`;;

let C1092IFH_PRED_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifcc_predecessorPoints] o
    check (fun th -> can (term_match [] `c1092ifcc_predecessorPoints a b c d e`) (concl th)));;

let C1092IFH_OPEN_TAC =
  REWRITE_TAC[c1092ifh_capInput; c1092ifcc_predecessorPoints] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`));;

(* Lean: reject_first *)
let C1092IFH_REJECT_FIRST = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\
     ABT_upper cC sC uC vC aC (--cC) (--sC) <= ABT_lower cW sW uW vW aW (--cC) (--sC)
     ==> false`,
  REPEAT GEN_TAC THEN C1092IFH_OPEN_TAC THEN C1092IFH_NORMAL_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092TFSU_UPPER_NEG]) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                `--(&7 / &20)`; `&7 / &20`; `--cC`; `--sC`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING;
    STRIP_TAC] THEN
  C1092IFH_LIN);;

(* Lean: positive_axes *)
let C1092IFH_POSITIVE_AXES = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\ c977cc_normal cW sW
     ==> vC + aC <= ABT_lower cW sW uW vW aW (--sC) cC \/
         ABT_upper cC sC uC vC aC (--sW) cW <= vW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFH_REJECT_FIRST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW` THEN
  C1092IFH_OPEN_TAC THEN C1092IFH_NORMAL_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  let cone rev nx ny =
    POP_ASSUM(fun th ->
      let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; nx; ny]
               C1092MIFP_UPWARD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[th'] THEN C1092MIFP_UNIT_TAC; ALL_TAC]) THEN
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092IFH_LIN in
  let take rev =
    POP_ASSUM(fun th ->
      let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
      MP_TAC th') THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[] in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [cone false `cC:real` `sC:real`;
    POP_ASSUM(fun th -> MP_TAC(REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th))) THEN
    ASM_REWRITE_TAC[];
    take false;
    cone true `sC:real` `--cC`;
    (* wu direct: the centre of C against the marker of W *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `&0`; `&0`; `cW:real`; `sW:real`] ABT_STRICT_BOUNDS) THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                  `--(&7 / &20)`; `&7 / &20`; `cW:real`; `sW:real`] ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092IFH_LIN;
    cone true `--cW` `--sW`;
    take false;
    cone true `sW:real` `--cW`]);;

(* Lean: positive_height (private) *)
let C1092IFH_POSITIVE_HEIGHT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\ c977cc_normal cW sW
     ==> vC + aC < &17 / &125`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFH_POSITIVE_AXES) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C1092IFCC_NONNEGATIVE_PREDECESSOR_FACES) THEN
  UNDISCH_TAC `c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW` THEN
  REWRITE_TAC[c1092ifh_capInput] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_TAC THEN
  C1092IFH_PRED_TAC THEN C1092IFH_NORMAL_TAC THEN
  (* kn, jn, sum, unit, ku *)
  C1092IFH_PROD `&0 <= (cC + sC) * cW` THEN
  C1092IFH_PROD `&0 <= (--sC) * (cW - sW)` THEN
  C1092IFH_PROD `&0 <= cC * sW` THEN
  C1092IFH_PROD `&0 <= (--sC) * cW` THEN
  C1092IFH_PROD `&0 < (cC - sC) * cW` THEN
  C1092IFH_PROD `&0 <= (cC + sC) * sW` THEN
  SUBGOAL_THEN `&0 <= cC * cW + sC * sW /\ &0 <= cC * sW - sC * cW /\
                &0 < (cC * sW - sC * cW) + (cC * cW + sC * sW)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C1092IFH_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `(cC * cW + sC * sW) pow 2 + (cC * sW - sC * cW) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `cC * cW + sC * sW <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `cC * sW - sC * cW`; SQ_NONNEG `(cC * cW + sC * sW) - &1`]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
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
      SUBGOAL_THEN `uW <= &0` ASSUME_TAC THENL
       [UNDISCH_TAC `linside cW sW uW vW aC (--(&7 / &20)) (&7 / &20)` THEN
        REWRITE_TAC[linside] THEN STRIP_TAC THEN C1092IFH_LIN; ALL_TAC] THEN
      C1092IFH_PROD `&0 <= (cC * sW - sC * cW) * (&0 - uW)` THEN
      C1092IFH_PROD `&0 <= (cC * cW + sC * sW) * (&43 / &500 - vW)` THEN
      C1092IFH_LIN;
      (* topU *)
      FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC o check (fun th ->
        is_conj(concl th) && is_disj(rand(concl th)))) THEN
      C1092IFH_PROD `&0 <= (cC * sW - sC * cW) * ((&543 / &500) * sW - aC - uW)` THEN
      C1092IFH_PROD `&0 < (aC - &1) * ((cC * sW - sC * cW) + (cC * cW + sC * sW))` THENL
       [C1092IFH_PROD `&0 <= (cC * cW + sC * sW) * (cW + sW - aC - vW)` THEN
        SUBGOAL_THEN `vC + aC < cC * ((cW + sW - &1) pow 2 / &2 + (&43 / &500) * sW pow 2) +
                                sC * (sW pow 2 + cW - sW - (&43 / &500) * cW * sW)`
          ASSUME_TAC THENL
         [SUBGOAL_THEN `cC * ((cW + sW - &1) pow 2 / &2 + (&43 / &500) * sW pow 2) +
                        sC * (sW pow 2 + cW - sW - (&43 / &500) * cW * sW) =
                        (cC * sW - sC * cW) * ((&543 / &500) * sW - &1) +
                        (cC * cW + sC * sW) * (cW + sW - &1)` SUBST1_TAC THENL
           [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; C1092IFH_LIN];
          ALL_TAC] THEN
        MP_TAC(SPECL [`cW:real`; `sW:real`] C1092IFCS_CAP_F0) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        C1092IFH_PROD `&0 < cC * (&13 / &100 - ((cW + sW - &1) pow 2 / &2 + (&43 / &500) * sW pow 2))` THEN
        C1092IFH_PROD `&0 <= (--sC) * (sW pow 2 + cW - sW - (&43 / &500) * cW * sW)` THEN
        C1092IFH_LIN;
        C1092IFH_PROD `&0 <= (cC * cW + sC * sW) * ((&543 / &500) * cW + sW - aC - vW)` THEN
        SUBGOAL_THEN `vC + aC < cC * (&43 / &500 + (cW + sW - &1) pow 2 / &2) +
                                sC * (sW pow 2 + cW - sW)` ASSUME_TAC THENL
         [SUBGOAL_THEN `cC * (&43 / &500 + (cW + sW - &1) pow 2 / &2) + sC * (sW pow 2 + cW - sW) =
                        (cC * sW - sC * cW) * ((&543 / &500) * sW - &1) +
                        (cC * cW + sC * sW) * ((&543 / &500) * cW + sW - &1)` SUBST1_TAC THENL
           [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; C1092IFH_LIN];
          ALL_TAC] THEN
        MP_TAC(SPECL [`cW:real`; `sW:real`] C1092IFCS_CAP_G0) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        C1092IFH_PROD `&0 < cC * (&247 / &2500 - (&43 / &500 + (cW + sW - &1) pow 2 / &2))` THEN
        C1092IFH_PROD `&0 <= (--sC) * (sW pow 2 + cW - sW)` THEN
        C1092IFH_LIN]];
    (* last *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
                  `--(cC * sW - sC * cW)`; `cC * cW + sC * sW`] C1092WS_UPPER_NP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFH_LIN;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    C1092IFH_PROD `&0 <= (cC * sW - sC * cW) * ((&7 / &50) * cC - sC / &2 - uC - aC)` THEN
    C1092IFH_PROD `&0 <= (cC * cW + sC * sW) * (vC + aC - &17 / &125)` THEN
    C1092IFH_PROD `&0 < (aC - &1) * (&1 + (cC * sW - sC * cW))` THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `sW:real`] C1092IFCS_CAP_OWN_POSITIVE) THEN
    ASM_REWRITE_TAC[c1092ifcs_centeredD] THEN DISCH_TAC THEN
    C1092IFH_LIN]);;

(* Lean: nonpositive_height (private) *)
let C1092IFH_NONPOSITIVE_HEIGHT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\ c977cc_normal cW (--sW)
     ==> vC + aC < &17 / &125`,
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
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092IFH_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092UTS_RELATIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&7 / &10 < cC * cW + sC * sW /\ cC * cW + sC * sW <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092IFH_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < uC + aC /\ &0 < --uC /\ &0 < vC + aC` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `ABT_upper`)) (concl th))) THENL
   [(* first: already excluded by reject_first when the disjunction was rewritten *)
    (* own *)
    ASM_CASES_TAC `sC * cW - cC * sW <= &0` THENL
     [MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC`; `cC:real`;
                    `--(sC * cW - cC * sW)`; `cC * cW + sC * sW`] C1092WS_LOWER_NN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFH_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      SUBGOAL_THEN `uW <= &0` ASSUME_TAC THENL
       [UNDISCH_TAC `linside cW sW uW vW aC (--(&7 / &20)) (&7 / &20)` THEN
        REWRITE_TAC[linside] THEN STRIP_TAC THEN C1092IFH_LIN; ALL_TAC] THEN
      C1092IFH_PROD `&0 <= (--(sC * cW - cC * sW)) * (&0 - uW)` THEN
      C1092IFH_PROD `&0 <= (cC * cW + sC * sW) * (&43 / &500 - vW)` THEN
      C1092IFH_LIN;
      MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC`; `cC:real`;
                    `--(sC * cW - cC * sW)`; `cC * cW + sC * sW`] C1092WS_LOWER_NP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFH_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFH_PROD `&0 <= (sC * cW - cC * sW) * (uW + cW - sW)` THEN
      C1092IFH_PROD `&0 <= (cC * cW + sC * sW) * ((&543 / &500) * cW - aC - vW)` THEN
      C1092IFH_PROD `&0 < (aC - &1) * ((sC * cW - cC * sW) + (cC * cW + sC * sW))` THEN
      SUBGOAL_THEN `vC + aC < cC * ((&43 / &500) * cW pow 2 + c1092mifs_f cW (--sW)) +
                              sC * (c1092mifs_g cW (--sW) + (&43 / &500) * cW * sW)`
        ASSUME_TAC THENL
       [SUBGOAL_THEN `cC * ((&43 / &500) * cW pow 2 + c1092mifs_f cW (--sW)) +
                      sC * (c1092mifs_g cW (--sW) + (&43 / &500) * cW * sW) =
                      (sC * cW - cC * sW) * (cW - sW - &1) +
                      (cC * cW + sC * sW) * ((&543 / &500) * cW - &1)` SUBST1_TAC THENL
         [REWRITE_TAC[c1092mifs_f; c1092mifs_g] THEN
          UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; C1092IFH_LIN];
        ALL_TAC] THEN
      MP_TAC(SPECL [`cW:real`; `--sW`] C1092IFCS_CAP_NEGATIVE_FG) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      C1092IFH_PROD `&0 < cC * (&17 / &125 - ((&43 / &500) * cW pow 2 + c1092mifs_f cW (--sW)))` THEN
      C1092IFH_PROD `&0 <= (--sC) * (c1092mifs_g cW (--sW) - (&43 / &500) * cW * --sW)` THEN
      C1092IFH_LIN];
    (* wu *)
    ASM_CASES_TAC `&0 <= sC * cW - cC * sW` THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--cW`; `--sW`;
                    `--(cC * cW + sC * sW)`; `sC * cW - cC * sW`] C1092WS_UPPER_NP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFH_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFH_PROD `&0 <= (cC * cW + sC * sW) * ((&7 / &50) * cC - sC / &2 - uC - aC)` THEN
      C1092IFH_PROD `&0 <= (sC * cW - cC * sW) * (vC + aC - &17 / &125)` THEN
      C1092IFH_PROD `&0 < (aC - &1) * (&1 + (cC * cW + sC * sW))` THEN
      MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092IFCS_CAP_LEFT_POSITIVE) THEN
      ASM_REWRITE_TAC[c1092ifcs_centeredD] THEN DISCH_TAC THEN
      C1092IFH_LIN;
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--cW`; `--sW`;
                    `--(cC * cW + sC * sW)`; `sC * cW - cC * sW`] C1092TFSU_UPPER_NEG_NEG) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFH_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFH_PROD `&0 <= (cC * cW + sC * sW) * ((&7 / &50) * cC - sC / &2 - uC - aC)` THEN
      C1092IFH_PROD `&0 <= (--(sC * cW - cC * sW)) * ((&7 / &20) * (cC + sC) - vC - aC)` THEN
      C1092IFH_PROD `&0 < (aC - &1) * (&1 + (cC * cW + sC * sW) - (sC * cW - cC * sW))` THEN
      MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092IFCS_CAP_LEFT_BEFORE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFH_LIN; ALL_TAC] THEN
      REWRITE_TAC[c1092ifcs_centeredD] THEN DISCH_TAC THEN
      C1092IFH_LIN];
    (* wv *)
    C1092IFH_PROD `&0 <= (cC * cW + sC * sW) * (vC + aC - &17 / &125)` THEN
    ASM_CASES_TAC `&0 <= sC * cW - cC * sW` THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
                    `sC * cW - cC * sW`; `cC * cW + sC * sW`] C1092TFSU_UPPER_POS_POS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFH_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFH_PROD `&0 <= (sC * cW - cC * sW) * (uC + aC)` THEN
      C1092IFH_LIN;
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
                    `sC * cW - cC * sW`; `cC * cW + sC * sW`] C1092WS_UPPER_NP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IFH_LIN;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      C1092IFH_PROD `&0 <= (--(sC * cW - cC * sW)) * (--uC)` THEN
      C1092IFH_LIN]]);;

(* Lean: centered_height_cap *)
let C1092IFH_CENTERED_HEIGHT_CAP = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW /\ abs sW <= cW
     ==> vC + aC < &17 / &125`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let vars = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
              `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] in
  ASM_CASES_TAC `&0 <= sW` THENL
   [MATCH_MP_TAC(SPECL vars C1092IFH_POSITIVE_HEIGHT);
    MATCH_MP_TAC(SPECL vars C1092IFH_NONPOSITIVE_HEIGHT)] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `abs sW <= cW` THEN REAL_ARITH_TAC);;

(* Lean: centered_caps *)
let C1092IFH_CENTERED_CAPS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aC /\ aC = aE /\ aC = aW /\ c977cc_normal cC (--sC) /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     c1092ifsu_negsucc cE sE uE vE aE /\ c1092ifcc_predecessorPoints cW sW uW vW aW /\
     abs sW <= cW /\
     ldisj cC sC uC vC aC cE sE uE vE aE /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> uC + aC <= (&7 / &50) * cC - sC / &2 /\ vC + aC < &17 / &125`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C1092IFCC_CENTERED_MARKER_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`]
    C1092IFCC_CENTERED_FIRST_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                      `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`]
                     C1092IFH_CENTERED_HEIGHT_CAP) THEN
  ASM_REWRITE_TAC[c1092ifh_capInput]);;
