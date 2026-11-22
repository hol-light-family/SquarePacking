(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalPredecessor.lean          *)
(* (N12Compact.C1092MPPMInwardFinal).  CENTERED-INWARD-OIOI sections 1-3.   *)
(* CenteredPredecessor is the predicate c1092mifp_centeredPredecessor;       *)
(* half is C1092WPS_half; f, g are c1092mifs_f, c1092mifs_g; upper/lower are *)
(* ABT_upper/ABT_lower.                                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalScalars.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;

let C1092MIFP_LIN = NLIN_TAC ~deg2:false [];;

let C1092MIFP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MIFP_LIN; ALL_TAC];;

let C1092MIFP_UNIT_TAC =
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  ASM_REAL_ARITH_TAC;;

(* the "upward" claim of upward_axes *)
let C1092MIFP_UPWARD = prove
 (`forall cC sC uC vC aC cW sW uW vW aW nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cW sW uW vW aW nx ny
     ==> &0 < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `--(&7 / &20)`; `--(&7 / &20)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `--(&7 / &20)`; `&7 / &20`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092MIFP_LIN);;

(* upward on the newest case hypothesis (optionally reversed), by contradiction *)
let C1092MIFP_CONE_TAC rev nx ny =
  POP_ASSUM(fun th ->
    let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; nx; ny]
             C1092MIFP_UPWARD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[th'] THEN C1092MIFP_UNIT_TAC; ALL_TAC]) THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN RASM_ARITH_TAC;;

let C1092MIFP_TAKE_TAC rev =
  POP_ASSUM(fun th ->
    let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
    MP_TAC th') THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[];;

(* Lean: upward_axes *)
let C1092MIFP_UPWARD_AXES = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     aC = aW /\ &0 < cC /\ sC <= &0 /\ &0 < cW /\ sW <= &0 /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> ABT_upper cC sC uC vC aC (--cC) (--sC) <= ABT_lower cW sW uW vW aW (--cC) (--sC) \/
         vC + aC <= ABT_lower cW sW uW vW aW (--sC) cC \/
         ABT_upper cC sC uC vC aC (--cW) (--sW) <= --(uW + aW) \/
         ABT_upper cC sC uC vC aC (--sW) cW <= vW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ABT_lower cW sW uW vW aC (--cW) (--sW) = --(uW + aC)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[C1092TFSU_LOWER_NEG]; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [C1092MIFP_CONE_TAC false `cC:real` `sC:real`;
    C1092MIFP_TAKE_TAC true;
    C1092MIFP_TAKE_TAC false;
    C1092MIFP_CONE_TAC true `sC:real` `--cC`;
    C1092MIFP_CONE_TAC false `cW:real` `sW:real`;
    C1092MIFP_TAKE_TAC true;
    C1092MIFP_TAKE_TAC false;
    C1092MIFP_CONE_TAC true `sW:real` `--cW`]);;

(* Lean: CenteredPredecessor (structure) *)
let c1092mifp_centeredPredecessor = new_definition
 `c1092mifp_centeredPredecessor cC sC uC vC aC cW sW uW vW aW <=>
    &1 < aC /\ aC = aW /\
    c977cc_normal cC (--sC) /\ sC < &0 /\ c977cc_normal cW (--sW) /\
    linside cC sC uC vC aC (&0) (&0) /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
    uC + aC <= (&7 / &20) * (cC - sC) /\
    uC + aC <= (&7 / &50) * cC - sC / &2 /\
    C1092WPS_half cC (--sC) < &21 / &100 /\
    --cW + sW <= uW /\ (&2 / &5) * cW + sW <= vW /\ vW + aW <= cW /\
    ldisj cC sC uC vC aC cW sW uW vW aW`;;

(* Lean: centered_predecessor_bound *)
let C1092MIFP_CENTERED_PREDECESSOR_BOUND = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092mifp_centeredPredecessor cC sC uC vC aC cW sW uW vW aW
     ==> vC + aC < cC * c1092mifs_f cW (--sW) + sC * c1092mifs_g cW (--sW)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mifp_centeredPredecessor] THEN STRIP_TAC THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  SUBGOAL_THEN `&0 < cC /\ &0 < cW` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092MIFP_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C1092MIFP_UPWARD_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MIFP_LIN; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cW:real`; `--sW:real`] C1092MIFS_PREDECESSOR_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MIFP_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC:real`; `cW:real`; `--sW:real`] C1092MIFS_RELATIVE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MIFP_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC:real`; `cW:real`; `--sW:real`] C1092MIFS_PREDECESSOR_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MIFP_PROD `&0 < cC * cW` THEN
  C1092MIFP_PROD `&0 <= --sC * --sW` THEN
  SUBGOAL_THEN `&0 < uC + aC /\ &0 < vC + aC` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vC + aC <= ABT_lower cW sW uW vW aC (--sC) cC` ASSUME_TAC THENL
   [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
     [(* first *)
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                    `--(&7 / &20)`; `&7 / &20`; `--cC:real`; `--sC:real`] ABT_STRICT_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MIFP_UNIT_TAC; STRIP_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[C1092TFSU_UPPER_NEG]) THEN
      MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092MIFP_LIN;
      ASM_REWRITE_TAC[];
      (* last *)
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--cW:real`; `--sW:real`;
                    `--(cC * cW + sC * sW)`; `sC * cW - cC * sW`] C1092WS_UPPER_NP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
        (REAL_ARITH_TAC ORELSE C1092MIFP_LIN); DISCH_TAC] THEN
      C1092MIFP_PROD `&0 <= (cC * cW + sC * sW) * ((&7 / &50) * cC - sC / &2 - (uC + aC))` THEN
      C1092MIFP_PROD `&0 < (sC * cW - cC * sW) * (vC + aC)` THEN
      C1092MIFP_PROD `&0 < (aC - &1) * (&1 + (cC * cW + sC * sW))` THEN
      MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092MIFP_LIN;
      (* lastV *)
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW:real`; `cW:real`;
                    `sC * cW - cC * sW`; `cC * cW + sC * sW`] C1092TFSU_UPPER_POS_POS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
        (REAL_ARITH_TAC ORELSE C1092MIFP_LIN); DISCH_TAC] THEN
      C1092MIFP_PROD `&0 < (sC * cW - cC * sW) * (uC + aC)` THEN
      C1092MIFP_PROD `&0 < (cC * cW + sC * sW) * (vC + aC)` THEN
      MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092MIFP_LIN];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC:real`; `cC:real`;
                `--(sC * cW - cC * sW)`; `cC * cW + sC * sW`] C1092WS_LOWER_NP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (REAL_ARITH_TAC ORELSE C1092MIFP_LIN); DISCH_TAC] THEN
  C1092MIFP_PROD `&0 <= (sC * cW - cC * sW) * (uW + cW - sW)` THEN
  C1092MIFP_PROD `&0 <= (cC * cW + sC * sW) * (cW - aC - vW)` THEN
  C1092MIFP_PROD `&0 < (aC - &1) * ((sC * cW - cC * sW) + (cC * cW + sC * sW))` THEN
  SUBGOAL_THEN `(sC * cW - cC * sW) * (cW - sW - &1) + (cC * cW + sC * sW) * (cW - &1) =
                cC * c1092mifs_f cW (--sW) + sC * c1092mifs_g cW (--sW)` (SUBST1_TAC o SYM)
  THENL
   [REWRITE_TAC[c1092mifs_f; c1092mifs_g] THEN
    UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  C1092MIFP_LIN);;

(* Lean: centered_predecessor *)
let C1092MIFP_CENTERED_PREDECESSOR = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092mifp_centeredPredecessor cC sC uC vC aC cW sW uW vW aW
     ==> vC + aC < cC / &11 + sC / &2 /\
         &49 / &50 < cC /\ --sC < &9 / &50 /\ C1092WPS_half cC (--sC) < &91 / &1000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MIFP_CENTERED_PREDECESSOR_BOUND) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mifp_centeredPredecessor] o
    check (fun th -> can (term_match [] `c1092mifp_centeredPredecessor a b c d e f g h i j`)
                         (concl th))) THEN
  MP_TAC(SPECL [`cW:real`; `--sW:real`] C1092MIFS_PREDECESSOR_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MIFP_LIN; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < vC + aC` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC:real`; `cW:real`; `--sW:real`; `vC + aC:real`]
    C1092MIFS_CENTERED_HEIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [C1092MIFP_LIN; ASM_REAL_ARITH_TAC]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC:real`] C1092MIFS_CENTERED_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
