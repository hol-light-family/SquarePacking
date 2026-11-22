(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardSmallThreeData.lean            *)
(* (N12Compact.C1092MPPMInwardSmallThree).  The three actual squares in     *)
(* SMALL-INWARD-THREE-SQUARE-ENDING.  Squares C = cC sC uC vC aC,            *)
(* B = cB sB uB vB aB, E = cE sE uE vE aE (OpenSquares: unit normal and      *)
(* 0 < side as explicit hypotheses).  Input is c1092istd_input (fields in    *)
(* Lean order); BottomAngle.Input = c1092ifbd_input, NegativeSuccessor =     *)
(* c1092ifsu_negsucc; Normal = c977cc_normal, normal_bounds =                *)
(* C977CC_NORMAL_BOUNDS; BottomAngle.angle = C1092IFBA_ANGLE, central_faces  *)
(* = C1092IFBD_CENTRAL_FACES; small_bounds / first_margin / last_margin,     *)
(* kappa, delta, FC, FE, Q: C1092ISTS_* / c1092ists_*; longitudinal_axes =  *)
(* C1092IFSU_LONGITUDINAL_AXES; lower_nn = C1092WS_LOWER_NN; upper_pos_neg = *)
(* C1092TFSU_UPPER_POS_NEG (lower / upper = ABT_lower / ABT_upper).          *)
(* Tag C1092ISTD_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardSmallThreeScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessor.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomData.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomAngle.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;

(* Lean: Input (structure) *)
let c1092istd_input = new_definition
 `c1092istd_input cC sC uC vC aC cB sB uB vB aB cE sE uE vE aE <=>
    c1092ifbd_input cC sC uC vC aC cB sB uB vB aB /\ aC = aE /\
    c1092ifsu_negsucc cE sE uE vE aE /\
    ldisj cC sC uC vC aC cE sE uE vE aE /\ ldisj cB sB uB vB aB cE sE uE vE aE`;;

let C1092ISTD_VARS = "cC sC uC vC aC cB sB uB vB aB cE sE uE vE aE";;
let C1092ISTD_HYP =
  "cC * cC + sC * sC = &1 /\\ &0 < aC /\\ cB * cB + sB * sB = &1 /\\ &0 < aB /\\ " ^
  "cE * cE + sE * sE = &1 /\\ &0 < aE /\\ " ^
  "c1092istd_input cC sC uC vC aC cB sB uB vB aB cE sE uE vE aE";;
let c1092istd_stmt c = parse_term (Printf.sprintf "!%s. %s ==> %s" C1092ISTD_VARS C1092ISTD_HYP c);;
let C1092ISTD_SQ = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                    `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;

let C1092ISTD_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092istd_input] o
    check (can (term_match [] `c1092istd_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifbd_input] o
    check (can (term_match [] `c1092ifbd_input a b c d e f g h i j`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (can (term_match [] `c1092ifsu_negsucc a b c d e`) o concl)) THEN
  C1092PRS_NORMAL_TAC;;

(* Lean: successor_low *)
let C1092ISTD_SUCCESSOR_LOW = prove
 (c1092istd_stmt "&1 / &3 < --sE",
  C1092ISTD_OPEN_TAC THEN
  SUBGOAL_THEN `&1 < --sE + (&343 / &500) * cE` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cE <= &1 - (--sE) pow 2 / &2` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - cE`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 / &3 - --sE) * (&1 - (&343 / &1000) * (--sE + &1 / &3))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

let C1092ISTD_K = `c1092ists_kappa cC (--sC) cE (--sE)`;;
let C1092ISTD_D = `c1092ists_delta cC (--sC) cE (--sE)`;;
let C1092ISTD_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092ISTD_B = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;
let C1092ISTD_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;
let C1092ISTD_LIN = NLIN_TAC ~deg2:false [];;
let C1092ISTD_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092ISTD_LIN; ALL_TAC];;
let C1092ISTD_SUBST_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`));;

(* Lean: successor_bounds *)
let C1092ISTD_SUCCESSOR_BOUNDS = prove
 (c1092istd_stmt "&15 / &17 < cE /\\ --sE < &8 / &17",
  C1092ISTD_OPEN_TAC THEN
  MP_TAC(SPECL (C1092ISTD_C @ C1092ISTD_B) C1092IFBA_ANGLE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092ISTS_SMALL_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092ISTD_SQ C1092ISTD_SUCCESSOR_LOW) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` C1092ISTD_K) ASSUME_TAC THENL
   [REWRITE_TAC[c1092ists_kappa] THEN
    C1092ISTD_PROD `&0 < cC * cE` THEN C1092ISTD_PROD `&0 <= --sC * --sE` THEN C1092ISTD_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` C1092ISTD_D) ASSUME_TAC THENL
   [REWRITE_TAC[c1092ists_delta] THEN
    C1092ISTD_PROD `&0 < (cC - &97 / &100) * --sE` THEN
    C1092ISTD_PROD `&0 <= --sC * (&1 - cE)` THEN C1092ISTD_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092ISTD_C @ C1092ISTD_B) C1092IFBD_CENTRAL_FACES) THEN
  ASM_REWRITE_TAC[c1092ifbd_faces] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--sE < &8 / &17` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092ISTS_FIRST_MARGIN) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; c1092ists_FC; c1092ists_Q] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092ISTS_LAST_MARGIN) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; c1092ists_FE; c1092ists_Q] THEN DISCH_TAC THEN
    C1092ISTD_PROD (mk_binop `(<):real->real->bool` `&0`
      (mk_binop `( * ):real->real->real` `aC - &1`
        (mk_binop `(+):real->real->real` `&1` (mk_binop `(+):real->real->real` C1092ISTD_K C1092ISTD_D)))) THEN
    MP_TAC(SPECL (C1092ISTD_C @ C1092ISTD_E) C1092IFSU_LONGITUDINAL_AXES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(SPECL (C1092ISTD_E @ [`cC:real`; `sC:real`; C1092ISTD_K; C1092ISTD_D]) C1092WS_LOWER_NN) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[c1092ists_kappa; c1092ists_delta] THEN
        CONJ_TAC THEN REAL_ARITH_TAC;
        DISCH_TAC] THEN
      C1092ISTD_PROD (mk_binop `(<=):real->real->bool` `&0`
        (mk_binop `( * ):real->real->real` C1092ISTD_K `(cE - sE) - (uE + aE)`)) THEN
      C1092ISTD_PROD (mk_binop `(<=):real->real->bool` `&0`
        (mk_binop `( * ):real->real->real` C1092ISTD_D `(--sE - &2 / &5 * cE) - (vE + aE)`)) THEN
      C1092ISTD_SUBST_TAC THEN C1092ISTD_LIN;
      MP_TAC(SPECL (C1092ISTD_C @ [`cE:real`; `sE:real`; C1092ISTD_K; mk_comb(`(--):real->real`, C1092ISTD_D)])
               C1092TFSU_UPPER_POS_NEG) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[c1092ists_kappa; c1092ists_delta] THEN
        REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
        UNDISCH_TAC (mk_binop `(<):real->real->bool` `&0` C1092ISTD_D) THEN
        REWRITE_TAC[c1092ists_delta] THEN REAL_ARITH_TAC;
        DISCH_TAC] THEN
      C1092ISTD_PROD (mk_binop `(<=):real->real->bool` `&0`
        (mk_binop `( * ):real->real->real` C1092ISTD_K `uC - (--cC - &2 / &5 * sC)`)) THEN
      C1092ISTD_PROD (mk_binop `(<=):real->real->bool` `&0`
        (mk_binop `( * ):real->real->real` C1092ISTD_D `--(vC + aC)`)) THEN
      C1092ISTD_SUBST_TAC THEN C1092ISTD_LIN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092ISTD_PROD `&0 < (&8 / &17 - --sE) * (&8 / &17 + --sE)` THEN
  NLIN_TAC [SQ_NONNEG `cE - &15 / &17`]);;
