(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOrdinaryNegativeHalfpoint.lean        *)
(* (N12Compact.C1092MPPMOrdinaryNegativeHalfpoint), full local Theorem 1.   *)
(* Squares C = cC sC uC vC aC (source), E = cE sE uE vE aE (successor).      *)
(* Frame is c1092onh_frame; scalars C1092ONH_*; faces C1092ONHF_*;           *)
(* support formulas C1092WS_FORMULAS; lower/upper ABT_lower/ABT_upper.       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryNegativeHalfpointFaces.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

let C1092ONHP_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092ONHP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092ONHP_LP_TAC; ALL_TAC];;

(* substitute proved values of max/min terms into the assumptions *)
let C1092ONHP_MM_TAC =
  ASSUM_LIST(fun ths ->
    let mm th = is_eq(concl th) &&
      (let l = lhand(concl th) in is_comb l &&
        (let f,_ = strip_comb l in f = `max:real->real->real` || f = `min:real->real->real`)) in
    let eqs = filter mm ths in
    RULE_ASSUM_TAC(fun th -> if mm th then th else REWRITE_RULE eqs th));;

let C1092ONHP_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092ONHP_LP_TAC; DISCH_TAC];;

(* Lean: point *)
let C1092ONHP_POINT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\
     &0 < cC /\ sC <= &0 /\ --sC <= cC /\ &0 < cE /\ sE <= &0 /\ --sE <= cE /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     --(&543 / &500) * cC <= uC /\ vC + aC <= (&7 / &20) * (cC + sC) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
     linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> linside cE sE uE vE aE (&1 / &2) (--(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C1092ONHF_NEGATIVE_FRAME) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`]
    C1092ONHF_NEGATIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C1092ONHP_USE C1092ONH_RELATIVE [`cC:real`; `--sC:real`; `cE:real`; `--sE:real`] THEN
  MP_TAC(SPECL [`cC:real`; `--sC:real`; `cE:real`; `--sE:real`]
    C1092ONH_SOURCE_COORDINATES) THEN
  ANTS_TAC THENL
  [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  C1092ONHP_USE C1092ONHF_MISSING_FACE [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] THEN
  C1092ONHP_USE C1092ONHF_AXES
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
     `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`]
    C1092WS_FORMULAS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`]
    C1092WS_FORMULAS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `min (cC * cE + sC * sE) (&0) = &0 /\
                max (cE * cC + sE * sC) (&0) = cE * cC + sE * sC`
  STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `&0 < cC * cE + --sC * --sE /\
      (cC * cE + --sC * --sE) pow 2 + (cC * --sE - --sC * cE) pow 2 = &1` THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  C1092ONHP_MM_TAC THEN
  C1092ONHP_PROD `&0 < (aC - &1) * (&1 + (cC * cE + --sC * --sE))` THEN
  ASM_CASES_TAC `&0 <= (cC * --sE - --sC * cE)` THENL
  [SUBGOAL_THEN `max (--cE * sC + sE * cC) (&0) = &0 /\ min (--cC * sE + sC * cE) (&0) = &0`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= (cC * --sE - --sC * cE)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   C1092ONHP_MM_TAC THEN
   C1092ONHP_PROD `&0 <= (cC * cE + --sC * --sE) * ((cE / &2 - sE) - (uE + aC))` THEN
   C1092ONHP_PROD `&0 <= (cC * --sE - --sC * cE) * --sE` THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C1092ONHP_PROD `&0 <= (cC * --sE - --sC * cE) * ((&13 / &50) * --sE - cE - vE)` THEN
    C1092ONHP_USE C1092ONH_C_POSITIVE [`cC:real`; `--sC:real`; `cE:real`; `--sE:real`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN C1092ONHP_LP_TAC;
    C1092ONHP_PROD `&0 <= (cC * cE + --sC * --sE) * (uC + (&543 / &500) * cC)` THEN
    C1092ONHP_PROD `&0 <= (cC * --sE - --sC * cE) * ((&7 / &20) * (cC + sC) - (vC + aC))` THEN
    C1092ONHP_PROD `&0 < (aC - &1) * (&1 + (cC * cE + --sC * --sE) + (cC * --sE - --sC * cE))` THEN
    C1092ONHP_USE C1092ONH_E_POSITIVE [`cC:real`; `--sC:real`; `cE:real`; `--sE:real`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN C1092ONHP_LP_TAC];
   SUBGOAL_THEN `max (--cE * sC + sE * cC) (&0) = --cE * sC + sE * cC /\
                 min (--cC * sE + sC * cE) (&0) = --cC * sE + sC * cE`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(&0 <= (cC * --sE - --sC * cE))` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   C1092ONHP_MM_TAC THEN
   C1092ONHP_PROD `&0 <= (cC * cE + --sC * --sE) * ((cE / &2 - sE) - (uE + aC))` THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C1092ONHP_PROD `&0 <= --(cC * --sE - --sC * cE) * ((vE + aC) + (&13 / &50) * cE)` THEN
    C1092ONHP_USE C1092ONH_C_NEGATIVE [`cC:real`; `--sC:real`; `cE:real`; `--sE:real`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN C1092ONHP_LP_TAC;
    C1092ONHP_PROD `&0 <= (cC * cE + --sC * --sE) * (uC + (&543 / &500) * cC)` THEN
    C1092ONHP_PROD `&0 <= --(cC * --sE - --sC * cE) * ((vC + aC) + (&7 / &20) * (cC + --sC))` THEN
    C1092ONHP_USE C1092ONH_E_NEGATIVE [`cC:real`; `--sC:real`; `cE:real`; `--sE:real`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN C1092ONHP_LP_TAC]]);;
