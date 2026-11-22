(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightNegativePairReach.lean (Jatloe).        *)
(* The final northeast sign sector: E (sE = --f) and T (sT = --s) both have  *)
(* negative canonical sine.  K, H, Q, L, P, G of the Lean proofs are written *)
(* out.                                                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperRightNegativeTopReach.ml";;
needs "n12/geometry/UpperRightNegativePairLongitudinalBounds.ml";;
needs "n12/geometry/UpperRightNegativePairBounds.ml";;

let URNPR_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let URNPR_FORM_TAC =
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS; C977NCO_LOWER_IN_BANDS] THEN
  (fun (asl,w as g) ->
     let abss = setify(find_terms (fun t -> is_comb t &&
                  rator t = `abs:real->real`) w) in
     let eqs = map (fun t -> let x = rand t in
        try TAC_PROOF((asl, mk_eq(t,x)), RASM_ARITH_TAC) with Failure _ ->
        TAC_PROOF((asl, mk_eq(t,mk_comb(`(--):real->real`,x))), RASM_ARITH_TAC))
        abss in
     (REWRITE_TAC eqs THEN REAL_ARITH_TAC) g);;

let URNPR_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --y` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let URNPR_MUL_NONPOS = prove
 (`forall a b. &0 <= a /\ b <= &0 ==> a * b <= &0`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:real`; `--b:real`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

let URNPR_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC];;

(* the sine of a negative square vanishes only for the axis frame *)
let URNPR_ZERO_SINE_TAC c s =
  SUBGOAL_THEN (mk_eq(s,`&0`)) ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(c,`&1`)) ASSUME_TAC THENL
  [UNDISCH_TAC (vsubst [c,`cc:real`; s,`ss:real`] `cc pow 2 + ss pow 2 = &1`) THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `c <= &1 /\ &1 <= c ==> c = &1`) THEN
   CONJ_TAC THEN NLIN_TAC []; ALL_TAC];;

(* Lean: longitudinal_growth (private) *)
let URNPR_LONGITUDINAL_GROWTH = prove
 (`forall cT sT uT vT aT s e f.
     cT * cT + sT * sT = &1 /\ &0 < aT /\ sT = --s /\
     c977cc_normal e f /\ c977cc_normal cT s /\ &1 < aT /\ lcont cT sT uT vT aT /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20)
     ==> (&7 / &2) * e - &3 * f < ABT_upper cT sT uT vT aT e (--f) + aT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`; `s:real`] URNTR_FACES) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`; `s:real`] URNTR_TOP_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sT:real = --s`)) THEN
  C977CSB_NORMAL_TAC THEN
  URNPR_UNFOLD_TAC `linside cT (--s) uT vT aT (&12 / &5) (&3)` THEN
  SUBGOAL_THEN `&0 < e * cT + f * s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= e * s - f * cT` THENL
  [SUBGOAL_THEN `ABT_upper cT (--s) uT vT aT e (--f) =
                 (e * cT + f * s) * (uT + aT) + (e * s - f * cT) * (vT + aT)`
   SUBST1_TAC THENL [URNPR_FORM_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`e:real`; `f:real`; `cT:real`; `s:real`] URNPLB_FORWARD_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    URNPR_PROD `&0 <= (e * cT + f * s) * (uT - ((&87 / &50) * cT - &3 * s))` THEN
    URNPR_PROD `&0 <= (e * s - f * cT) * (vT - (&47 / &20) * (cT + s))` THEN
    SUBGOAL_THEN `&0 < ((e * cT + f * s) + (e * s - f * cT) + &1) * (aT - &1)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(e * cT + f * s) * ((&87 / &50) * cT - &3 * s) +
      (e * s - f * cT) * ((&47 / &20) * (cT + s)) + (e * cT + f * s) +
      (e * s - f * cT) + &1 - ((&7 / &2) * e - &3 * f) =
      &1 + e * (cT + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * cT * s) +
      f * (s - cT + &13 / &20 - (&13 / &20) * s pow 2 - (&61 / &100) * cT * s)`
    MP_TAC THENL
    [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`e:real`; `f:real`; `cT:real`; `s:real`] URNPLB_FORWARD_UPPER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    URNPR_PROD `&0 <= (e * cT + f * s) * (s * uT - cT * (vT + aT) + &4)` THEN
    URNPR_PROD `&0 <= e * (vT - (&3 * cT + (&87 / &50) * s))` THEN
    URNPR_PROD `&0 <= s * (e * cT + f * s)` THEN
    SUBGOAL_THEN `&0 < (e + s * (e * cT + f * s) + s) * (aT - &1)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < y - x ==> x < y`) THEN
    MATCH_MP_TAC URNPR_POS_OF_MUL THEN EXISTS_TAC `s:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `s * ((((e * cT + f * s) * (uT + aT) + (e * s - f * cT) * (vT + aT)) + aT) -
           ((&7 / &2) * e - &3 * f)) =
      (e * cT + f * s) * (s * uT - cT * (vT + aT) + &4) +
      e * (vT - (&3 * cT + (&87 / &50) * s)) +
      (aT - &1) * (e + s * (e * cT + f * s) + s) +
      (s + e * (&1 - cT - (&44 / &25) * s + cT * s) + f * (s pow 2 - s))` MP_TAC THENL
    [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC];
   SUBGOAL_THEN `ABT_upper cT (--s) uT vT aT e (--f) =
                 (e * cT + f * s) * (uT + aT) + (e * s - f * cT) * vT`
   SUBST1_TAC THENL [URNPR_FORM_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`e:real`; `f:real`; `cT:real`; `s:real`] URNPLB_FORWARD_ROW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    URNPR_PROD `&0 <= (e * cT + f * s) * (uT - ((&87 / &50) * cT - &3 * s))` THEN
    URNPR_PROD `&0 <= --(e * s - f * cT) * (((&12 / &5) * s + &3 * cT) - vT)` THEN
    SUBGOAL_THEN `&0 < ((e * cT + f * s) + &1) * (aT - &1)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(e * cT + f * s) * ((&87 / &50) * cT - &3 * s) +
      (e * s - f * cT) * ((&12 / &5) * s + &3 * cT) + (e * cT + f * s) + &1 -
      ((&7 / &2) * e - &3 * f) =
      &1 + e * (cT - &44 / &25 + (&33 / &50) * s pow 2) + f * (s - (&33 / &50) * cT * s)`
    MP_TAC THENL
    [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`e:real`; `f:real`; `cT:real`; `s:real`] URNPLB_FORWARD_REVERSE_UPPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    URNPR_PROD `&0 <= (e * cT + f * s) * (s * uT - cT * (vT + aT) + &4)` THEN
    URNPR_PROD `&0 <= e * (vT - (&3 * cT + (&87 / &50) * s))` THEN
    URNPR_PROD `&0 <= s * (e * cT + f * s)` THEN
    URNPR_PROD `&0 <= s * --(e * s - f * cT)` THEN
    SUBGOAL_THEN `&0 < (e + s * (e * cT + f * s) + s - s * (e * s - f * cT)) * (aT - &1)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < y - x ==> x < y`) THEN
    MATCH_MP_TAC URNPR_POS_OF_MUL THEN EXISTS_TAC `s:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `s * ((((e * cT + f * s) * (uT + aT) + (e * s - f * cT) * vT) + aT) -
           ((&7 / &2) * e - &3 * f)) =
      (e * cT + f * s) * (s * uT - cT * (vT + aT) + &4) +
      e * (vT - (&3 * cT + (&87 / &50) * s)) +
      (aT - &1) * (e + s * (e * cT + f * s) + s - s * (e * s - f * cT)) +
      (s + e * (&1 - cT - (&44 / &25) * s + cT * s) + f * (s pow 2 - s) -
       s * (e * s - f * cT))` MP_TAC THENL
    [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]]);;

(* Lean: top_longitudinal_impossible (private) *)
let URNPR_TOP_LONGITUDINAL_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cT sT uT vT aT f s.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     sE = --f /\ sT = --s /\ c977cc_normal cE f /\ c977cc_normal cT s /\
     aE = aT /\ &1 < aE /\ lcont cT sT uT vT aT /\
     uE + aE <= (&7 / &2) * cE - &3 * f /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&3) (&7 / &2) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
     uT + aT <= ABT_lower cE sE uE vE aE cT (--s)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aT`)) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`] URNTR_FACES) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`] URNTR_TOP_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sT:real = --s`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sE:real = --f`)) THEN
  C977CSB_NORMAL_TAC THEN
  URNPR_UNFOLD_TAC `linside cE (--f) uE vE aE (&3) (&3)` THEN
  URNPR_UNFOLD_TAC `linside cE (--f) uE vE aE (&3) (&7 / &2)` THEN
  SUBGOAL_THEN `&0 < cE * cT + f * s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  URNPR_PROD `&0 <= (cE * cT + f * s) * (((&7 / &2) * cE - &3 * f) - uE - aE)` THEN
  ASM_CASES_TAC `&0 <= cE * s - f * cT` THENL
  [SUBGOAL_THEN `ABT_lower cE (--f) uE vE aE cT (--s) =
                 (cE * cT + f * s) * uE - (cE * s - f * cT) * (vE + aE)` ASSUME_TAC THENL
   [URNPR_FORM_TAC; ALL_TAC] THEN
   URNPR_PROD `&0 <= (cE * s - f * cT) * ((vE + aE) - (&3 * f + (&7 / &2) * cE))` THEN
   SUBGOAL_THEN
    `aE * (&1 + (cE * cT + f * s)) + uT - (cE * cT + f * s) * ((&7 / &2) * cE - &3 * f) +
     (cE * s - f * cT) * (&3 * f + (&7 / &2) * cE) <= &0` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `&1 + (cE * cT + f * s) + ((&87 / &50) * cT - &3 * s) -
     (cE * cT + f * s) * ((&7 / &2) * cE - &3 * f) +
     (cE * s - f * cT) * (&3 * f + (&7 / &2) * cE) =
     &1 + cT * (cE - &44 / &25 + (&1 / &2) * f pow 2 - (&1 / &2) * cE * f) +
     s * (f + &1 / &2 - (&1 / &2) * f pow 2 - (&1 / &2) * cE * f)` ASSUME_TAC THENL
   [UNDISCH_TAC `cE pow 2 + f pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`cE:real`; `f:real`; `cT:real`; `s:real`] URNPLB_REVERSE_PARALLEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (&1 + (cE * cT + f * s)) * (aE - &1)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cE:real`; `f:real`; `cT:real`; `s:real`] URNPLB_REVERSE_PARALLEL_TOP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `s * (aE * (&1 + (cE * cT + f * s)) + uT -
           (cE * cT + f * s) * ((&7 / &2) * cE - &3 * f) +
           (cE * s - f * cT) * (&3 * f + (&7 / &2) * cE)) <= &0` ASSUME_TAC THENL
    [MATCH_MP_TAC URNPR_MUL_NONPOS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    URNPR_PROD `&0 <= cT * (vT - (&3 * cT + (&87 / &50) * s))` THEN
    URNPR_PROD `&0 <= s * (&1 + (cE * cT + f * s))` THEN
    SUBGOAL_THEN `&0 < (cT + s * (&1 + (cE * cT + f * s))) * (aE - &1)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `cT * (&3 * cT + (&87 / &50) * s) - s * ((&87 / &50) * cT - &3 * s) = &3 /\
      s * (&1 + (cE * cT + f * s) + ((&87 / &50) * cT - &3 * s) -
           (cE * cT + f * s) * ((&7 / &2) * cE - &3 * f) +
           (cE * s - f * cT) * (&3 * f + (&7 / &2) * cE)) =
      s * (&1 + cT * (cE - &44 / &25 + (&1 / &2) * f pow 2 - (&1 / &2) * cE * f) +
           s * (f + &1 / &2 - (&1 / &2) * f pow 2 - (&1 / &2) * cE * f))` MP_TAC THENL
    [CONJ_TAC THENL
     [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    RASM_ARITH_TAC];
   SUBGOAL_THEN `ABT_lower cE (--f) uE vE aE cT (--s) =
                 (cE * cT + f * s) * uE - (cE * s - f * cT) * vE` ASSUME_TAC THENL
   [URNPR_FORM_TAC; ALL_TAC] THEN
   URNPR_PROD `&0 <= --(cE * s - f * cT) * ((&3 * f + &3 * cE) - vE)` THEN
   SUBGOAL_THEN
    `aE * (&1 + (cE * cT + f * s)) + uT - (cE * cT + f * s) * ((&7 / &2) * cE - &3 * f) +
     (cE * s - f * cT) * (&3 * f + &3 * cE) <= &0` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `&1 + (cE * cT + f * s) + ((&87 / &50) * cT - &3 * s) -
     (cE * cT + f * s) * ((&7 / &2) * cE - &3 * f) +
     (cE * s - f * cT) * (&3 * f + &3 * cE) =
     &1 + cT * (cE - &63 / &50 - cE pow 2 / &2) + s * f * (&1 - cE / &2)` ASSUME_TAC THENL
   [UNDISCH_TAC `cE pow 2 + f pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`cE:real`; `f:real`; `cT:real`; `s:real`] URNPLB_REVERSE_ROW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (&1 + (cE * cT + f * s)) * (aE - &1)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cE:real`; `f:real`; `cT:real`; `s:real`] URNPLB_REVERSE_ROW_TOP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `s * (aE * (&1 + (cE * cT + f * s)) + uT -
           (cE * cT + f * s) * ((&7 / &2) * cE - &3 * f) +
           (cE * s - f * cT) * (&3 * f + &3 * cE)) <= &0` ASSUME_TAC THENL
    [MATCH_MP_TAC URNPR_MUL_NONPOS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    URNPR_PROD `&0 <= cT * (vT - (&3 * cT + (&87 / &50) * s))` THEN
    URNPR_PROD `&0 <= s * (&1 + (cE * cT + f * s))` THEN
    SUBGOAL_THEN `&0 < (cT + s * (&1 + (cE * cT + f * s))) * (aE - &1)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `cT * (&3 * cT + (&87 / &50) * s) - s * ((&87 / &50) * cT - &3 * s) = &3 /\
      s * (&1 + (cE * cT + f * s) + ((&87 / &50) * cT - &3 * s) -
           (cE * cT + f * s) * ((&7 / &2) * cE - &3 * f) +
           (cE * s - f * cT) * (&3 * f + &3 * cE)) =
      s * (&1 + cT * (cE - &63 / &50 - cE pow 2 / &2) + s * f * (&1 - cE / &2))` MP_TAC THENL
    [CONJ_TAC THENL
     [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    RASM_ARITH_TAC]]);;

(* Lean: corner_transverse_impossible (private) *)
let URNPR_CORNER_TRANSVERSE_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cT sT uT vT aT f s.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     sE = --f /\ sT = --s /\ c977cc_normal cE f /\ c977cc_normal cT s /\
     aE = aT /\ &1 < aE /\ lcont cE sE uE vE aE /\ lcont cT sT uT vT aT /\
     uE + aE <= (&7 / &2) * cE - &3 * f /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
     ABT_upper cT sT uT vT aT f cE <= vE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aT`)) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`] URNTR_FACES) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`] URNTR_TOP_WALL) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `f:real`] URNTR_TOP_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sT:real = --s`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sE:real = --f`)) THEN
  C977CSB_NORMAL_TAC THEN
  URNPR_UNFOLD_TAC `linside cT (--s) uT vT aE (&12 / &5) (&3)` THEN
  SUBGOAL_THEN `&0 < cE * cT + f * s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  URNPR_PROD `&0 <= f * (((&7 / &2) * cE - &3 * f) - (uE + aE))` THEN
  URNPR_PROD `&0 <= cE * (vE - ABT_upper cT (--s) uT vT aE f cE)` THEN
  SUBGOAL_THEN `cE * ABT_upper cT (--s) uT vT aE f cE + aE * (cE + f) - &4 -
                f * ((&7 / &2) * cE - &3 * f) <= &0` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= cE * s - f * cT` THENL
  [SUBGOAL_THEN `ABT_upper cT (--s) uT vT aE f cE =
                 --(cE * s - f * cT) * uT + (cE * cT + f * s) * (vT + aE)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [URNPR_FORM_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`cE:real`; `f:real`; `cT:real`; `s:real`] URNPB_PLUS) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   URNPR_PROD `&0 <= (cE * (cE * cT + f * s)) * (vT - (&47 / &20) * (cT + s))` THEN
   URNPR_PROD `&0 <= (cE * (cE * s - f * cT)) * (((&12 / &5) * cT - &3 * s) - uT)` THEN
   URNPR_PROD `&0 <= cE * (cE * cT + f * s)` THEN
   SUBGOAL_THEN `&0 < (cE * (cE * cT + f * s) + (cE + f)) * (aE - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `cE * (--(cE * s - f * cT) * ((&12 / &5) * cT - &3 * s) +
           (cE * cT + f * s) * ((&47 / &20) * (cT + s))) +
     cE * (cE * cT + f * s) + (cE + f) - &4 - f * ((&7 / &2) * cE - &3 * f) =
     cE + f - &33 / &20 + (&13 / &20) * f pow 2 +
     cE pow 2 * (cT + (&13 / &20) * s pow 2 - (&1 / &20) * cT * s) +
     cE * f * (s - &11 / &10 - (&1 / &20) * s pow 2 - (&13 / &20) * cT * s)` MP_TAC THENL
   [UNDISCH_TAC `cE pow 2 + f pow 2 = &1` THEN UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC;
   SUBGOAL_THEN `cE * s <= f * cT` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `ABT_upper cT (--s) uT vT aE f cE =
                 --(cE * s - f * cT) * (uT + aE) + (cE * cT + f * s) * (vT + aE)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [URNPR_FORM_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`cE:real`; `f:real`; `cT:real`; `s:real`] URNPB_MINUS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    URNPR_PROD `&0 <= (cE * --(cE * s - f * cT)) * (uT - ((&87 / &50) * cT - &3 * s))` THEN
    URNPR_PROD `&0 <= (cE * (cE * cT + f * s)) * (vT - (&47 / &20) * (cT + s))` THEN
    URNPR_PROD `&0 <= cE * ((cE * cT + f * s) - (cE * s - f * cT))` THEN
    SUBGOAL_THEN `&0 < (cE * ((cE * cT + f * s) - (cE * s - f * cT)) + (cE + f)) * (aE - &1)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `cE * (--(cE * s - f * cT) * ((&87 / &50) * cT - &3 * s) +
            (cE * cT + f * s) * ((&47 / &20) * (cT + s))) +
      cE * ((cE * cT + f * s) - (cE * s - f * cT)) + (cE + f) - &4 -
      f * ((&7 / &2) * cE - &3 * f) =
      cE + f - &33 / &20 + (&13 / &20) * f pow 2 +
      cE pow 2 * (cT - s + (&13 / &20) * s pow 2 + (&61 / &100) * cT * s) +
      cE * f * (cT + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * cT * s)`
    MP_TAC THENL
    [UNDISCH_TAC `cE pow 2 + f pow 2 = &1` THEN UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN
     CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
     URNPR_ZERO_SINE_TAC `cT:real` `s:real` THEN
     UNDISCH_TAC `--s * uT + cT * (vT + aE) <= &4` THEN
     UNDISCH_TAC `&3 * cT + (&87 / &50) * s <= vT` THEN
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `f:real`; `cT:real`; `s:real`] URNPB_UPPER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    URNPR_PROD `&0 <= (cE * --(cE * s - f * cT)) * (s * uT - cT * (vT + aE) + &4)` THEN
    URNPR_PROD `&0 <= (cE * f) * (vT - (&3 * cT + (&87 / &50) * s))` THEN
    URNPR_PROD `&0 <= cE * f` THEN
    URNPR_PROD `&0 <= (cE * s) * --(cE * s - f * cT)` THEN
    SUBGOAL_THEN `&0 < s * (cE + f)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (cE * f - cE * s * (cE * s - f * cT) + s * (cE + f)) * (aE - &1)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `s * (cE * (--(cE * s - f * cT) * (uT + aE) + (cE * cT + f * s) * (vT + aE)) +
           aE * (cE + f) - &4 - f * ((&7 / &2) * cE - &3 * f)) <= &0` ASSUME_TAC THENL
    [MATCH_MP_TAC URNPR_MUL_NONPOS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
     `s * (cE * (--(cE * s - f * cT) * (uT + aE) + (cE * cT + f * s) * (vT + aE)) +
           aE * (cE + f) - &4 - f * ((&7 / &2) * cE - &3 * f)) =
      cE * --(cE * s - f * cT) * (s * uT - cT * (vT + aE) + &4) +
      cE * f * (vT - (&3 * cT + (&87 / &50) * s)) +
      (aE - &1) * (cE * f - cE * s * (cE * s - f * cT) + s * (cE + f)) +
      (cE * f * (&1 - cT) + s * (cE + f - f pow 2 + cE * f * (cT - &44 / &25) -
                                 cE pow 2 * s))` MP_TAC THENL
    [UNDISCH_TAC `cE pow 2 + f pow 2 = &1` THEN UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN
     CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]]);;

(* Lean: point *)
let URNPR_POINT = prove
 (`forall cE sE uE vE aE cT sT uT vT aT f s.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     sE = --f /\ sT = --s /\ c977cc_normal cE f /\ c977cc_normal cT s /\
     aE = aT /\ &1 < aE /\ lcont cE sE uE vE aE /\ lcont cT sT uT vT aT /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     linside cE sE uE vE aE (&3) (&7 / &2) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
     ldisj cE sE uE vE aE cT sT uT vT aT
     ==> linside cE sE uE vE aE (&7 / &2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aT`)) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `uE + aE <= (&7 / &2) * cE - &3 * f` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cE sE uE vE aE (&7 / &2) (&3)` THEN
   FIRST_ASSUM(fun th -> if concl th = `sE:real = --f` then REWRITE_TAC[th] else NO_TAC) THEN
   C977CSB_NORMAL_TAC THEN
   URNPR_UNFOLD_TAC `linside cE sE uE vE aE (&3) (&3)` THEN
   URNPR_UNFOLD_TAC `linside cE sE uE vE aE (&16 / &5) (&3)` THEN
   URNPR_UNFOLD_TAC `linside cE sE uE vE aE (&3) (&7 / &2)` THEN
   ASM_REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`;
                `cE:real`; `f:real`] URNPR_LONGITUDINAL_GROWTH) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `f:real`; `s:real`]
    URNPR_TOP_LONGITUDINAL_IMPOSSIBLE) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `f:real`; `s:real`]
    URNPR_CORNER_TRANSVERSE_IMPOSSIBLE) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`] URNTR_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sT:real = --s`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sE:real = --f`)) THEN
  C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`cE:real`; `--f:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `--f:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cT:real`; `--s:real`; `uT:real`; `vT:real`; `aE:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cT:real`; `--s:real`; `uT:real`; `vT:real`; `aE:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `--f:real`; `uE:real`; `vE:real`; `aE:real`;
                `cT:real`; `--s:real`; `uT:real`; `vT:real`; `aE:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let sep nx ny = SPECL [`cE:real`; `--f:real`; `uE:real`; `vE:real`; `aE:real`;
                   `cT:real`; `--s:real`; `uT:real`; `vT:real`; `aE:real`; nx; ny]
                  ABT_SEPARATED in
  let sb sq x y nx ny =
    let c,s',u,v = sq in
    MP_TAC(SPECL [c; s'; u; v; `aE:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     ASM_REAL_ARITH_TAC; STRIP_TAC] in
  let qE = (`cE:real`,`--f:real`,`uE:real`,`vE:real`)
  and qT = (`cT:real`,`--s:real`,`uT:real`,`vT:real`) in
  let use_sep nx ny swap radius =
    MP_TAC(sep nx ny) THEN ANTS_TAC THENL
    [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
      else ALL_TAC) THEN
     MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC[]; ALL_TAC] in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [use_sep `cE:real` `--f:real` false
     (SPECL [`cE:real`; `--f:real`; `aE:real`; `cT:real`; `--s:real`; `aE:real`]
       ABT_PARALLEL_RADIUS) THEN
   sb qE `&3` `&3` `cE:real` `--f:real` THEN
   sb qT `&2` `&1543 / &500` `cE:real` `--f:real` THEN
   DISCH_THEN DISJ_CASES_TAC THEN RASM_ARITH_TAC;
   use_sep `-- --f:real` `cE:real` false
     (SPECL [`cE:real`; `--f:real`; `aE:real`; `cT:real`; `--s:real`; `aE:real`]
       ABT_TRANSVERSE_RADIUS) THEN
   sb qE `&3` `&7 / &2` `-- --f:real` `cE:real` THEN
   sb qT `&12 / &5` `&3` `-- --f:real` `cE:real` THEN
   DISCH_THEN DISJ_CASES_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_NEG_NEG] THEN
   ASM_REWRITE_TAC[];
   use_sep `cT:real` `--s:real` true
     (SPECL [`cT:real`; `--s:real`; `aE:real`; `cE:real`; `--f:real`; `aE:real`]
       ABT_PARALLEL_RADIUS) THEN
   sb qE `&3` `&3` `cT:real` `--s:real` THEN
   sb qT `&2` `&1543 / &500` `cT:real` `--s:real` THEN
   DISCH_THEN DISJ_CASES_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[];
   use_sep `-- --s:real` `cT:real` true
     (SPECL [`cT:real`; `--s:real`; `aE:real`; `cE:real`; `--f:real`; `aE:real`]
       ABT_TRANSVERSE_RADIUS) THEN
   sb qE `&3` `&3` `-- --s:real` `cT:real` THEN
   sb qT `&12 / &5` `&3` `-- --s:real` `cT:real` THEN
   DISCH_THEN DISJ_CASES_TAC THEN RASM_ARITH_TAC]);;
