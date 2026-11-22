(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMSteepPositiveSuccessorFarCap.lean    *)
(* (N12Compact.C1092MPPMSteepPositiveSuccessorFarCap).                       *)
(* STEEP-POSITIVE-SUCCESSOR-FAR-CAP Theorem 1.  Scalars: C1092SFC_*;          *)
(* kappa / sigma / relative_bounds: c1092prs_* / C1092PRS_RELATIVE_BOUNDS;   *)
(* positive_axes / upper_pn / upper_nonpositive: C1092MEI_*;                 *)
(* lower_pn / lower_nn / formulas: C1092WS_*; upper_nn: C1092MEA_UPPER_NN.   *)
(* C is cC sC uC vC aC, the recipient E is cE sE uE vE aE.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveSuccessorFarCapScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMElbowIsolation.ml";;

let C1092SPFC_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SPFC_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SPFC_LIN_TAC; DISCH_TAC];;

let C1092SPFC_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SPFC_LIN_TAC; DISCH_TAC];;

let C1092SPFC_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092SPFC_LIN_TAC;;

let C1092SPFC_FORMULA_TAC th args =
  MP_TAC(SPECL args th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    (fun (asl,w as g) -> if is_eq w then
       (REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN C1092SPFC_LIN_TAC) g
     else C1092SPFC_LIN_TAC g);
    DISCH_TAC];;

(* lower support of a square in a direction with both coordinates nonpositive *)
let C1092SPFC_LOWER_NONPOSITIVE = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ d <= &0 /\ e <= &0
     ==> ABT_lower c s u v a nx ny = d * (u + a) + e * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `d <= &0 ==> min d (&0) = d`] THEN REAL_ARITH_TAC);;

(* Lean: Input (structure) *)
let c1092spfc_input = new_definition
 `c1092spfc_input cC sC uC vC aC cE sE uE vE aE <=>
    &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ &3 / &5 <= sC /\ c977cc_normal cE sE /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    --cC - sC <= uC /\ uC + aC <= &0 /\
    (&14 / &25) * sC - cC <= vC /\ vC + aC <= (&543 / &500) * sC /\
    vE + aE <= &0 /\
    (forall y. --(&14 / &25) <= y ==> y <= --(&2 / &5) ==> ~linside cE sE uE vE aE (&1) y) /\
    ldisj cC sC uC vC aC cE sE uE vE aE`;;

(* unfold the input; aE is replaced by aC *)
let C1092SPFC_INPUT_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spfc_input] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "c1092spfc_input"
                     with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> let t = concl th in not(is_neg t) && not(is_forall t) &&
       can (find_term ((=) `linside`)) t) ths));;

let C1092SPFC_HYPS =
 `cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
  c1092spfc_input cC sC uC vC aC cE sE uE vE aE`;;

(* Lean: bar_bands (private) *)
let C1092SPFC_BAR_BANDS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE y.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092spfc_input cC sC uC vC aC cE sE uE vE aE /\
     --(&14 / &25) <= y /\ y <= --(&2 / &5)
     ==> uE < cE + sE * y /\ --sE + cE * y < vE + aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SPFC_INPUT_TAC THEN
  C1092SPFC_LE_MUL_TAC `sE:real` `y + &14 / &25` THEN
  C1092SPFC_LE_MUL_TAC `cE:real` `--(&2 / &5) - y` THEN
  CONJ_TAC THEN C1092SPFC_LIN_TAC);;

let C1092SPFC_BANDS_TAC y =
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; y]
    C1092SPFC_BAR_BANDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
                  REPEAT CONJ_TAC THEN C1092SPFC_LIN_TAC; STRIP_TAC];;

(* Lean: near_cap (private) *)
let C1092SPFC_NEAR_CAP = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092spfc_input cC sC uC vC aC cE sE uE vE aE
     ==> uE + aE <= cE - (&2 / &5) * sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092SPFC_BANDS_TAC `--(&2 / &5)` THEN
  C1092SPFC_INPUT_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--(&2 / &5)` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `&14 / &25`)) (concl th))) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN
  REPEAT CONJ_TAC THEN C1092SPFC_LIN_TAC);;

(* Lean: bar_vertex (private) *)
let C1092SPFC_BAR_VERTEX = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092spfc_input cC sC uC vC aC cE sE uE vE aE /\
     cE - (&14 / &25) * sE < uE + aE /\
     --sE - (&14 / &25) * cE <= vE /\ &0 < sE
     ==> cE * (uE + aE) - sE * vE <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092SPFC_NEAR_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spfc_input] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "c1092spfc_input"
                     with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  SUBGOAL_THEN `&0 < cE` ASSUME_TAC THENL [C1092SPFC_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists f. cE * f = vE + sE` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(vE + sE) / cE` THEN UNDISCH_TAC `&0 < cE` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `exists w. sE * w = uE + aE - cE` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(uE + aE - cE) / sE` THEN UNDISCH_TAC `&0 < sE` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&14 / &25) <= f /\ w <= --(&2 / &5)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
     [C1092SPFC_LT_MUL_TAC `cE:real` `--(&14 / &25) - f`;
      C1092SPFC_LT_MUL_TAC `sE:real` `w + &2 / &5`] THEN
    C1092SPFC_LIN_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cE * sE * (w - f) = cE * (uE + aE) - sE * vE - &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cE * f = vE + sE` THEN UNDISCH_TAC `sE * w = uE + aE - cE` THEN
    UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `f < w` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092SPFC_LT_MUL_TAC `cE:real` `sE:real` THEN
    C1092SPFC_LE_MUL_TAC `cE * sE` `f - w` THEN C1092SPFC_LIN_TAC; ALL_TAC] THEN
  C1092SPFC_BANDS_TAC `(f + w) / &2` THEN
  C1092SPFC_LT_MUL_TAC `cE:real` `(f + w) / &2 - f` THEN
  C1092SPFC_LT_MUL_TAC `sE:real` `w - (f + w) / &2` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(f + w) / &2` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `&14 / &25`)) (concl th))) THEN
  ANTS_TAC THENL [C1092SPFC_LIN_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [C1092SPFC_LIN_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092SPFC_LIN_TAC);;

(* Lean: competing_faces (private) *)
let C1092SPFC_COMPETING_FACES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092spfc_input cC sC uC vC aC cE sE uE vE aE /\
     cE - (&14 / &25) * sE < uE + aE
     ==> uE < --(&11 / &25) /\ --(&13 / &125) < vE + aE /\ vE < --(&1) /\
         &0 < uE + aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092SPFC_BANDS_TAC `--(&14 / &25)` THEN
  SUBGOAL_THEN `--sE - (&14 / &25) * cE <= vE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spfc_input] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "c1092spfc_input"
                       with Failure _ -> false)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--(&14 / &25)` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&14 / &25`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN
    REPEAT CONJ_TAC THEN C1092SPFC_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sE` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spfc_input] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "c1092spfc_input"
                       with Failure _ -> false)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
      check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
    C1092SPFC_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092SPFC_BAR_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] C1092SFC_WALL_WIDTH) THEN
  C1092SPFC_INPUT_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092SPFC_LE_MUL_TAC `sE:real` `--(vE + aC)` THEN
  C1092SPFC_LT_MUL_TAC `aC - &1` `cE + sE` THEN
  SUBGOAL_THEN `uE < --(&11 / &25)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092SPFC_LE_MUL_TAC `cE:real` `uE + &11 / &25` THEN C1092SPFC_LIN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092SPFC_LIN_TAC);;

(* Lean: competing_impossible (private) *)
let C1092SPFC_COMPETING_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092spfc_input cC sC uC vC aC cE sE uE vE aE /\
     cE - (&14 / &25) * sE < uE + aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    C1092SPFC_COMPETING_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092SPFC_INPUT_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `aC:real`; `uC:real`; `vC:real`] C1092SFC_CENTRAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092PRS_RELATIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[c1092prs_kappa; c1092prs_sigma] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092MEI_POSITIVE_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092SPFC_LIN_TAC; DISCH_TAC] THEN
  (* own supports *)
  C1092SPFC_FORMULA_TAC C1092MEI_UPPER_NONPOSITIVE
   [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `sC:real`; `--cC`; `&0`; `--(&1)`] THEN
  C1092SPFC_FORMULA_TAC C1092WS_LOWER_PN
   [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sE:real`; `--cE`; `&0`; `--(&1)`] THEN
  C1092SPFC_LT_MUL_TAC `cC * cE + sC * sE` `(uC + aC) + &83 / &200` THEN
  C1092SPFC_LT_MUL_TAC `cC * cE + sC * sE` `--vC - &29 / &125` THEN
  C1092SPFC_LT_MUL_TAC `cC * cE + sC * sE` `--(&11 / &25) - uE` THEN
  C1092SPFC_LT_MUL_TAC `cC * cE + sC * sE` `(vE + aC) + &13 / &125` THEN
  ASM_CASES_TAC `&0 <= cC * sE - sC * cE` THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092SFC_CLOSE_ORDER) THEN
    ASM_REWRITE_TAC[c1092prs_kappa; c1092prs_sigma] THEN STRIP_TAC THEN
    C1092SPFC_LE_MUL_TAC `cC * sE - sC * cE` `(uC + aC) + &83 / &200` THEN
    C1092SPFC_LE_MUL_TAC `cC * sE - sC * cE` `vC + aC` THEN
    C1092SPFC_LE_MUL_TAC `cC * sE - sC * cE` `uE + aC` THEN
    C1092SPFC_LE_MUL_TAC `cC * sE - sC * cE` `(vE + aC) + &13 / &125` THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
     [C1092SPFC_FORMULA_TAC C1092WS_LOWER_PN
       [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
        `cC * cE + sC * sE`; `--(cC * sE - sC * cE)`] THEN C1092SPFC_LIN_TAC;
      C1092SPFC_FORMULA_TAC C1092SPFC_LOWER_NONPOSITIVE
       [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`; `--cC`;
        `--(cC * sE - sC * cE)`; `--(cC * cE + sC * sE)`] THEN C1092SPFC_LIN_TAC;
      C1092SPFC_FORMULA_TAC C1092MEA_UPPER_NN
       [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`;
        `cC * cE + sC * sE`; `cC * sE - sC * cE`] THEN C1092SPFC_LIN_TAC;
      C1092SPFC_FORMULA_TAC C1092MEI_UPPER_PN
       [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `sE:real`; `--cE`;
        `cC * sE - sC * cE`; `--(cC * cE + sC * sE)`] THEN C1092SPFC_LIN_TAC];
    SUBGOAL_THEN `cC * sE - sC * cE <= &0` ASSUME_TAC THENL
     [UNDISCH_TAC `~(&0 <= cC * sE - sC * cE)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092SFC_EARLIER_WEIGHT) THEN
    ASM_REWRITE_TAC[c1092prs_kappa; c1092prs_sigma] THEN DISCH_TAC THEN
    C1092SPFC_LE_MUL_TAC `--(cC * sE - sC * cE)` `--(&1) - vE` THEN
    C1092SPFC_LE_MUL_TAC `--(cC * sE - sC * cE)` `--vC` THEN
    C1092SPFC_LE_MUL_TAC `--(cC * sE - sC * cE)` `--uC` THEN
    C1092SPFC_LE_MUL_TAC `--(cC * sE - sC * cE)` `--uE` THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
     [C1092SPFC_FORMULA_TAC C1092WS_LOWER_NN
       [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
        `cC * cE + sC * sE`; `--(cC * sE - sC * cE)`] THEN C1092SPFC_LIN_TAC;
      C1092SPFC_FORMULA_TAC C1092WS_LOWER_PN
       [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`; `--cC`;
        `--(cC * sE - sC * cE)`; `--(cC * cE + sC * sE)`] THEN C1092SPFC_LIN_TAC;
      C1092SPFC_FORMULA_TAC C1092MEI_UPPER_PN
       [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`;
        `cC * cE + sC * sE`; `cC * sE - sC * cE`] THEN C1092SPFC_LIN_TAC;
      C1092SPFC_FORMULA_TAC C1092MEI_UPPER_NONPOSITIVE
       [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `sE:real`; `--cE`;
        `cC * sE - sC * cE`; `--(cC * cE + sC * sE)`] THEN C1092SPFC_LIN_TAC]]);;

(* Lean: upper_cap *)
let C1092SPFC_UPPER_CAP = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092spfc_input cC sC uC vC aC cE sE uE vE aE
     ==> uE + aE <= cE - (&14 / &25) * sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    C1092SPFC_COMPETING_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;
