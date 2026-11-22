(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCenteredPositiveHeightAxes.lean      *)
(* (namespace N12Compact.C1092MPPMCenteredPositive).  The complete actual    *)
(* C--W separating-axis list for a nonnegative center-owned C.               *)
(* HeightInput is the predicate c1092cpha_heightInput; PredecessorPoints is  *)
(* c1092ifcc_predecessorPoints; Normal is c977cc_normal; upper/lower are     *)
(* ABT_upper/ABT_lower; C1092TwoFifths.Support.reverse / lower_neg are       *)
(* C1092TFSU_REVERSE / C1092TFSU_LOWER_NEG; the axis split                   *)
(* (faceSeparation_of_disjoint + separated + radius identities) is           *)
(* ABT_FOUR_AXES.  The private lemma upward is C1092MIFP_UPWARD (the same    *)
(* statement, proved in MPPMInwardFinalPredecessor); center_reject is        *)
(* C1092CPHA_CENTER_REJECT.  Tag C1092CPHA_.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_MPPMCenteredPositiveHeightScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalPredecessor.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCenteredCaps.ml";;

let C1092CPHA_LIN = NLIN_TAC ~deg2:false [];;

let C1092CPHA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: HeightInput (structure) *)
let c1092cpha_heightInput = new_definition
 `c1092cpha_heightInput (cC:real) (sC:real) (uC:real) (vC:real) (aC:real)
                        (cW:real) (sW:real) (uW:real) (vW:real) (aW:real) <=>
    &1 < aC /\
    aC = aW /\
    c977cc_normal cC sC /\
    &99 / &100 < cC /\
    sC < &7 / &50 /\
    linside cC sC uC vC aC (&0) (&0) /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    uC + aC <= (&7 / &50) * cC - sC / &2 /\
    c1092ifcc_predecessorPoints cW sW uW vW aW /\
    ldisj cC sC uC vC aC cW sW uW vW aW`;;

(* Lean: upward (private): C1092MIFP_UPWARD, restated for HeightInput *)
let C1092CPHA_UPWARD = prove
 (`forall cC sC uC vC aC cW sW uW vW aW nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092cpha_heightInput cC sC uC vC aC cW sW uW vW aW /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cW sW uW vW aW nx ny
     ==> &0 < ny`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1092cpha_heightInput; c1092ifcc_predecessorPoints] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `nx:real`; `ny:real`]
    C1092MIFP_UPWARD) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: center_reject (private) *)
let C1092CPHA_CENTER_REJECT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092cpha_heightInput cC sC uC vC aC cW sW uW vW aW /\
     nx pow 2 + ny pow 2 = &1 /\ ny <= nx /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cW sW uW vW aW nx ny
     ==> false`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1092cpha_heightInput; c1092ifcc_predecessorPoints] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `&0`; `&0`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                `--(&7 / &20)`; `&7 / &20`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092CPHA_LIN);;

(* the case tactics: the newest assumption is a separation on an axis *)
let C1092CPHA_UNIT_TAC =
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);;

(* after the setup, aW is replaced by aC *)
let C1092CPHA_SQ = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`];;

let C1092CPHA_REV th = REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th);;

let C1092CPHA_CONE_TAC rev nx ny =
  POP_ASSUM(fun th ->
    let th' = if rev then C1092CPHA_REV th else th in
    MP_TAC(SPECL (C1092CPHA_SQ @ [nx; ny]) C1092CPHA_UPWARD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[th'] THEN C1092CPHA_UNIT_TAC; ALL_TAC]) THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092CPHA_LIN;;

let C1092CPHA_REJECT_TAC nx ny =
  POP_ASSUM(fun th ->
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC(SPECL (C1092CPHA_SQ @ [nx; ny]) C1092CPHA_CENTER_REJECT) THEN
    ASM_REWRITE_TAC[th] THEN REPEAT CONJ_TAC THEN
    FIRST [C1092CPHA_UNIT_TAC; C1092CPHA_LIN]);;

let C1092CPHA_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092cpha_heightInput] o
    check (fun th -> can (term_match [] `c1092cpha_heightInput a b c d e f g h i j`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  C1092CPHA_NORMAL_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL C1092CPHA_SQ ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC);;

(* Lean: positive_height_axes *)
let C1092CPHA_POSITIVE_HEIGHT_AXES = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092cpha_heightInput cC sC uC vC aC cW sW uW vW aW /\ c977cc_normal cW sW
     ==> vC + aC <= ABT_lower cW sW uW vW aW (--sC) cC \/
         ABT_upper cC sC uC vC aC (--sW) cW <= vW`,
  C1092CPHA_SETUP_TAC THENL
   [C1092CPHA_REJECT_TAC `cC:real` `sC:real`;
    C1092CPHA_CONE_TAC true `--cC` `--sC`;
    POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    C1092CPHA_CONE_TAC true `sC:real` `--cC`;
    C1092CPHA_REJECT_TAC `cW:real` `sW:real`;
    C1092CPHA_CONE_TAC true `--cW` `--sW`;
    POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    C1092CPHA_CONE_TAC true `sW:real` `--cW`]);;

(* Lean: nonpositive_height_axes *)
let C1092CPHA_NONPOSITIVE_HEIGHT_AXES = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092cpha_heightInput cC sC uC vC aC cW sW uW vW aW /\ c977cc_normal cW (--sW)
     ==> vC + aC <= ABT_lower cW sW uW vW aW (--sC) cC \/
         ABT_upper cC sC uC vC aC (--cW) (--sW) <= --(uW + aW) \/
         ABT_upper cC sC uC vC aC (--sW) cW <= vW`,
  C1092CPHA_SETUP_TAC THENL
   [C1092CPHA_REJECT_TAC `cC:real` `sC:real`;
    C1092CPHA_CONE_TAC true `--cC` `--sC`;
    POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    C1092CPHA_CONE_TAC true `sC:real` `--cC`;
    C1092CPHA_CONE_TAC false `cW:real` `sW:real`;
    POP_ASSUM(MP_TAC o MATCH_MP C1092TFSU_REVERSE) THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_OWNU) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[C1092TFSU_LOWER_NEG; CONJUNCT2 th]) THEN
    MESON_TAC[];
    POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    C1092CPHA_CONE_TAC true `sW:real` `--cW`]);;
