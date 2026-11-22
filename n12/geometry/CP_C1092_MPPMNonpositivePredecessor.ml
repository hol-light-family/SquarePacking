(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNonpositivePredecessor.lean           *)
(* (N12Compact.C1092MPPMNonpositivePredecessor).  Completed local producer   *)
(* behind ORDINARY-NEGATIVE-HALFPOINT Corollary 2.  Squares                  *)
(* C = cC sC uC vC aC (predecessor), E = cE sE uE vE aE (successor).         *)
(* Frame: c1092onh_frame; scalars C1092NPP_*; faces C1092ONHF_*; the        *)
(* Theorem 1 point C1092ONHP_POINT; MissingPositiveFaces c1092mmpf_inputs /  *)
(* C1092MMPF_PROFILE; formulas C1092WS_*; upper_neg/lower_neg               *)
(* C1092MCSUP_NEGATIVE_SUPPORT; SAT step ABT_FOUR_AXES.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessorScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryNegativeHalfpoint.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveFaces.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let C1092NPPT_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092NPPT_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092NPPT_LP_TAC; ALL_TAC];;

let C1092NPPT_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
                  FIRST [REAL_ARITH_TAC; C1092NPPT_LP_TAC]; DISCH_THEN STRIP_ASSUME_TAC];;

let C1092NPPT_MM_TAC =
  ASSUM_LIST(fun ths ->
    let mm th = is_eq(concl th) &&
      (let l = lhand(concl th) in is_comb l &&
        (let f,_ = strip_comb l in f = `max:real->real->real` || f = `min:real->real->real`)) in
    let eqs = filter mm ths in
    RULE_ASSUM_TAC(fun th -> if mm th then th else REWRITE_RULE eqs th));;

let C1092NPPT_USE_D th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
                  FIRST [REAL_ARITH_TAC; C1092NPPT_LP_TAC]; DISCH_TAC];;

(* the goal F from an excluded point ~linside q x y (unfolding) *)
let C1092NPPT_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN C1092NPPT_LP_TAC;;

let C1092NPPT_FRAMES_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c1092onh_frame x y`) o concl) ths in
    MAP_EVERY (fun th ->
      let th' = REWRITE_RULE[c1092onh_frame] th in
      STRIP_ASSUME_TAC (MATCH_MP CCCS_BOUNDS th') THEN STRIP_ASSUME_TAC th') ns);;

(* Lean: PositiveRegimes (structure) *)
let c1092nppt_positiveRegimes = new_definition
 `c1092nppt_positiveRegimes c s u v a <=>
    v + a <= s + (&13 / &50) * c /\
    (--c - s <= u \/
     (--(&543 / &500) * c <= u /\ &99 / &100 < c /\ s < &9 / &100) \/
     (v + a <= (&543 / &500) * s /\ --(&13 / &50) * c < u + a /\
      &49 / &50 < c /\ s < &9 / &50))`;;

let C1092NPPT_SQS = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                     `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`];;

(* the local `cone` of positive_axes *)
let C1092NPPT_CONE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `--(&7 / &20)`; `--(&7 / &20)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `&7 / &20`; `--(&7 / &20)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092NPPT_LP_TAC);;

let C1092NPPT_CONE_REV = prove
 (`forall cC sC uC vC aC cE sE uE vE aE nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cE sE uE vE aE nx ny <= ABT_lower cC sC uC vC aC nx ny
     ==> &0 < --nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092NPPT_CONE THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--ny:real`] THEN
  ASM_REWRITE_TAC[C1092MCSUP_NEGATIVE_SUPPORT] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN ASM_REAL_ARITH_TAC);;

(* Lean: positive_axes *)
let C1092NPPT_POSITIVE_AXES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     aC = aE /\ c1092onh_frame cC sC /\ c1092onh_frame cE (--sE) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> uC + aC <= ABT_lower cE sE uE vE aE cC sC \/
         --vC <= ABT_lower cE sE uE vE aE sC (--cC) \/
         ABT_upper cC sC uC vC aC cE sE <= uE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092NPPT_FRAMES_TAC THEN
  let rw th nx ny =
    MP_TAC(SPECL (C1092NPPT_SQS @ [nx; ny]) th) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     RASM_ARITH_TAC;
     RASM_ARITH_TAC] in
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                `sC:real`; `--cC:real`] C1092MCSUP_NEGATIVE_SUPPORT) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         rw C1092NPPT_CONE_REV `cC:real` `sC:real`;
         rw C1092NPPT_CONE `--sC:real` `cC:real`;
         DISJ2_TAC THEN DISJ1_TAC THEN RASM_ARITH_TAC;
         rw C1092NPPT_CONE_REV `cE:real` `sE:real`;
         rw C1092NPPT_CONE_REV `--sE:real` `cE:real`;
         MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                       `--(&7 / &20)`; `--(&7 / &20)`; `--sE:real`; `cE:real`] ABT_STRICT_BOUNDS) THEN
         MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                       `&13 / &50`; `--(&1)`; `--sE:real`; `cE:real`] ABT_STRICT_BOUNDS) THEN
         ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
         ANTS_TAC THENL [RASM_ARITH_TAC; STRIP_TAC] THEN
         ANTS_TAC THENL [RASM_ARITH_TAC; STRIP_TAC] THEN RASM_ARITH_TAC]);;

(* Lean: positive_point *)
let C1092NPPT_POSITIVE_POINT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c1092onh_frame cC sC /\ c1092onh_frame cE (--sE) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     c1092nppt_positiveRegimes cC sC uC vC aC /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
     linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> linside cE sE uE vE aE (&1 / &2) (--(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092NPPT_USE_D C1092NPPT_POSITIVE_AXES
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
     `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  C1092NPPT_USE C1092ONHF_MISSING_FACE [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] THEN
  C1092NPPT_USE C1092NPP_RELATIVE [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] THEN
  C1092NPPT_FRAMES_TAC THEN
  FIRST_X_ASSUM((fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2 th)) o
    REWRITE_RULE[c1092nppt_positiveRegimes] o
    check (fun th -> can (term_match [] `c1092nppt_positiveRegimes a b c d e`) (concl th))) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) then th
                           else REWRITE_RULE[linside] th) THEN
  SUBGOAL_THEN `cC * (cE * cE + sE * sE) = cC /\ sC * (cE * cE + sE * sE) = sC /\
                cE * (cC * cC + sC * sC) = cE /\ sE * (cC * cC + sC * sC) = sE`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`]
    C1092WS_FORMULAS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`; `--cC:real`]
    C1092WS_FORMULAS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`]
    C1092WS_FORMULAS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `min (cC * cE + sC * sE) (&0) = &0 /\ min (--cC * sE + sC * cE) (&0) = &0 /\
    min (sC * cE + --cC * sE) (&0) = &0 /\
    min (--sC * sE + --cC * cE) (&0) = --sC * sE + --cC * cE /\
    max (cE * cC + sE * sC) (&0) = cE * cC + sE * sC /\
    max (--cE * sC + sE * cC) (&0) = &0` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092NPPT_MM_TAC THEN
  C1092NPPT_PROD `&0 <= (cC * cE - sC * --sE) * ((cE / &2 - sE) - (uE + aC))` THEN
  C1092NPPT_PROD `&0 <= (cC * --sE + sC * cE) * ((cE / &2 - sE) - (uE + aC))` THEN
  C1092NPPT_PROD `&0 <= (cC * --sE + sC * cE) * (((&13 / &50) * --sE - cE) - vE)` THEN
  C1092NPPT_PROD `&0 <= (cC * cE - sC * --sE) * ((vE + aC) - --(&13 / &50) * cE)` THEN
  C1092NPPT_PROD `&0 <= (cC * --sE + sC * cE) * ((sC + (&13 / &50) * cC) - (vC + aC))` THEN
  C1092NPPT_PROD `&0 < (aC - &1) * (&1 + (cC * cE - sC * --sE))` THEN
  C1092NPPT_PROD `&0 < (aC - &1) * (&1 + (cC * --sE + sC * cE))` THEN
  C1092NPPT_PROD `&0 < (aC - &1) * (&1 + (cC * cE - sC * --sE) + (cC * --sE + sC * cE))` THEN
  C1092NPPT_PROD `&0 <= (aC - &1) * (cC * cE - sC * --sE)` THEN
  C1092NPPT_USE C1092NPP_TRANSVERSE [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] THEN
  C1092NPPT_USE C1092NPP_FIRST_SOURCE [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] THEN
  C1092NPPT_USE C1092NPP_THIRD_SOURCE [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] THEN
  C1092NPPT_USE C1092NPP_FIRST_TARGET [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `ABT_lower cE sE uE vE aC cC sC`)) (concl th))) THENL
  [FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN STRIP_ASSUME_TAC) o
     check (fun th -> is_disj(concl th) &&
       can (find_term ((=) `--cC - sC <= uC`)) (concl th))) THENL
   [C1092NPPT_LP_TAC;
    C1092NPPT_USE C1092NPP_SECOND_SOURCE [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] THEN
    C1092NPPT_LP_TAC;
    C1092NPPT_LP_TAC];
   C1092NPPT_LP_TAC;
   FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN STRIP_ASSUME_TAC) o
     check (fun th -> is_disj(concl th) &&
       can (find_term ((=) `--cC - sC <= uC`)) (concl th))) THENL
   [C1092NPPT_PROD `&0 <= (cC * cE - sC * --sE) * (uC - (--cC - sC))` THEN
    C1092NPPT_LP_TAC;
    C1092NPPT_PROD `&0 <= (cC * cE - sC * --sE) * (uC - --(&543 / &500) * cC)` THEN
    C1092NPPT_USE C1092NPP_SECOND_TARGET [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] THEN
    C1092NPPT_LP_TAC;
    C1092NPPT_PROD `&0 <= (cC * --sE + sC * cE) * ((&543 / &500) * sC - (vC + aC))` THEN
    C1092NPPT_PROD `&0 <= (cC * cE - sC * --sE) * ((uC + aC) - --(&13 / &50) * cC)` THEN
    C1092NPPT_USE C1092NPP_THIRD_TARGET [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] THEN
    C1092NPPT_LP_TAC]]);;

(* Lean: positive_forward_regimes *)
let C1092NPPT_POSITIVE_FORWARD_REGIMES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092onh_frame c s /\
               linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
               linside c s u v a (--(&1)) (--(&13 / &50)) /\
               linside c s u v a (--(&1)) (--(&2 / &5)) /\
               linside c s u v a (--(&13 / &50)) (&0) /\
               ~linside c s u v a (--(&1)) (--(&1)) /\
               ~linside c s u v a (--(&543 / &500)) (&0) /\
               ~linside c s u v a (--(&1)) (&13 / &50)
               ==> c1092nppt_positiveRegimes c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NPPT_FRAMES_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  REWRITE_TAC[c1092nppt_positiveRegimes] THEN
  SUBGOAL_THEN `v + a <= s + (&13 / &50) * c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092NPPT_MISS_TAC `~linside c s u v a (--(&1)) (&13 / &50)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `--c - s <= u` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s - c <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092NPPT_MISS_TAC `~linside c s u v a (--(&1)) (--(&1))`; ALL_TAC] THEN
  ASM_CASES_TAC `--(&543 / &500) * c <= u` THENL
  [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `s < &9 / &100` ASSUME_TAC THENL [C1092NPPT_LP_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092NPPT_PROD `&0 < (&9 / &100 - s) * (&9 / &100 + s)` THEN
   C1092NPPT_PROD `&0 <= (&99 / &100 - c) * (&99 / &100 + c)` THEN
   C1092NPPT_LP_TAC;
   DISJ2_TAC THEN
   SUBGOAL_THEN `v + a <= (&543 / &500) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NPPT_MISS_TAC `~linside c s u v a (--(&543 / &500)) (&0)`; ALL_TAC] THEN
   SUBGOAL_THEN `&1 < c + (&43 / &500) * s` ASSUME_TAC THENL [C1092NPPT_LP_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [C1092NPPT_LP_TAC; ALL_TAC] THEN
   C1092NPPT_PROD `&0 < (c + (&43 / &500) * s - &1) * (c + &1)` THEN
   SUBGOAL_THEN `&0 < (&43 / &500) * (&1 + c) - s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092NPPT_PROD `&0 <= s * --((&43 / &500) * (&1 + c) - s)` THEN C1092NPPT_LP_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `s < &9 / &50` ASSUME_TAC THENL [C1092NPPT_LP_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [C1092NPPT_LP_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092NPPT_PROD `&0 < (&9 / &50 - s) * (&9 / &50 + s)` THEN
   C1092NPPT_PROD `&0 <= (&49 / &50 - c) * (&49 / &50 + c)` THEN
   C1092NPPT_LP_TAC]);;

(* Lean: negative_missing_caps *)
let C1092NPPT_NEGATIVE_MISSING_CAPS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092onh_frame c (--s) /\
               linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
               linside c s u v a (--(&1)) (--(&13 / &50)) /\
               linside c s u v a (--(&1)) (--(&2 / &5)) /\
               linside c s u v a (--(&1)) (--(&1 / &2)) /\
               ~linside c s u v a (--(&1)) (--(&1)) /\
               ~linside c s u v a (--(&543 / &500)) (&0) /\
               ~linside c s u v a (--(&13 / &50)) (&0)
               ==> --(&543 / &500) * c <= u /\ v + a <= (&7 / &20) * (c + s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NPPT_FRAMES_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  SUBGOAL_THEN `s - c <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092NPPT_MISS_TAC `~linside c s u v a (--(&1)) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&543 / &500) * c <= u` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `v + a <= (&543 / &500) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NPPT_MISS_TAC `~linside c s u v a (--(&543 / &500)) (&0)`; ALL_TAC] THEN
   C1092NPPT_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&13 / &50) * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `u + a <= --(&13 / &50) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NPPT_MISS_TAC `~linside c s u v a (--(&13 / &50)) (&0)`; ALL_TAC] THEN
   C1092NPPT_LP_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C1092NPPT_LP_TAC);;

(* Lean: Inputs (structure) *)
let c1092nppt_inputs = new_definition
 `c1092nppt_inputs cC sC uC vC aC cE sE uE vE aE <=>
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
    linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\
    ~linside cC sC uC vC aC (--(&1)) (--(&1)) /\
    ~linside cC sC uC vC aC (--(&543 / &500)) (&0) /\
    ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
    ~linside cC sC uC vC aC (--(&1)) (&13 / &50) /\
    (~linside cC sC uC vC aC (--(&13 / &50)) (&0) ==> c1092mmpf_inputs cC sC uC vC aC) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
    ldisj cC sC uC vC aC cE sE uE vE aE`;;

(* Lean: point *)
let C1092NPPT_POINT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ &0 < cC /\ abs sC <= cC /\
     &0 < cE /\ sE <= &0 /\ --sE <= cE /\
     c1092nppt_inputs cC sC uC vC aC cE sE uE vE aE
     ==> linside cE sE uE vE aE (&1 / &2) (--(&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092nppt_inputs] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--sC <= cC /\ sC <= cC` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `abs sC <= cC` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092NPPT_USE C1092ONHF_NEGATIVE_FRAME [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] THEN
  ASM_CASES_TAC `sC <= &0` THENL
  [C1092NPPT_USE C1092ONHF_NEGATIVE_FRAME [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN
   SUBGOAL_THEN `--(&543 / &500) * cC <= uC /\ vC + aC <= (&7 / &20) * (cC + sC)`
   STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `linside cC sC uC vC aC (--(&13 / &50)) (&0)` THENL
    [MATCH_MP_TAC C1092ONHF_FORWARD_OWNED_CAPS THEN ASM_REWRITE_TAC[];
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
     ASM_REWRITE_TAC[c1092mmpf_inputs] THEN STRIP_TAC THEN
     MATCH_MP_TAC C1092NPPT_NEGATIVE_MISSING_CAPS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   MATCH_MP_TAC C1092ONHP_POINT THEN
   MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN
   ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
   SUBGOAL_THEN `c1092onh_frame cC sC` ASSUME_TAC THENL
   [REWRITE_TAC[c1092onh_frame; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c1092nppt_positiveRegimes cC sC uC vC aC` ASSUME_TAC THENL
   [ASM_CASES_TAC `linside cC sC uC vC aC (--(&13 / &50)) (&0)` THENL
    [MATCH_MP_TAC C1092NPPT_POSITIVE_FORWARD_REGIMES THEN ASM_REWRITE_TAC[];
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MMPF_PROFILE) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[c1092mmpf_faces; c1092nppt_positiveRegimes] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
   MATCH_MP_TAC C1092NPPT_POSITIVE_POINT THEN
   MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN
   ASM_REWRITE_TAC[]]);;
