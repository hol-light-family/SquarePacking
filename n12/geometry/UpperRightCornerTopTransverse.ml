(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightCornerTopTransverse.lean (Jatloe).      *)
(* The top square's transverse axis cannot separate it from a positive       *)
(* northeast corner which misses the farther outer point.                    *)
(* K = cE*cT + sE*sT and H = cE*sT - sE*cT are written out.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperRightCornerReachAxes.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let URCTT_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: small_sine (private) *)
let URCTT_SMALL_SINE = prove
 (`forall e f. c977cc_normal e f ==> f <= &5 / &7`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal e f` THEN REWRITE_TAC[c977cc_normal] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: parallel_margin (private) *)
let URCTT_PARALLEL_MARGIN = prove
 (`forall e f. c977cc_normal e f ==> &0 < &1 - (&3 / &5) * (e + f)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: shallow_margin (private) *)
let URCTT_SHALLOW_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ e * s - f * c <= &0
     ==> &0 <= c * (e - (&3 / &5) * e pow 2) + s * (f - &3 / &5 - (&3 / &5) * e * f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URCTT_SMALL_SINE) THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URCTT_PARALLEL_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `f - &3 / &5 - (&3 / &5) * e * f <= &0` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= f * (e - &7 / &10)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `e:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `e * ((c * (e - (&3 / &5) * e pow 2) + s * (f - &3 / &5 - (&3 / &5) * e * f)) - &0) =
    c * (&1 - (&3 / &5) * (e + f)) + (e * s - f * c) * (f - &3 / &5 - (&3 / &5) * e * f)`
  SUBST1_TAC THENL
  [UNDISCH_TAC `e pow 2 + f pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC(REAL_ARITH `&0 <= --a * --b ==> &0 <= a * b`) THEN
   MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

(* Lean: steep_lower_margin (private) *)
let URCTT_STEEP_LOWER_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ &0 <= e * s - f * c
     ==> &0 <= (e * c + f * s) * (&1 - f / &2) - (&3 / &5) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URCTT_SMALL_SINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `c <= e * c + f * s` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
   MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `e:real` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `e * (((e * c + f * s) - c) - &0) = c * (&1 - e) + f * (e * s - f * c)`
   SUBST1_TAC THENL
   [UNDISCH_TAC `e pow 2 + f pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (e * c + f * s - c) * (&1 - f / &2) /\
                &0 <= c * (&2 / &5 - f / &2)` MP_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: steep_upper_margin (private) *)
let URCTT_STEEP_UPPER_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ &0 <= e * s - f * c
     ==> &0 <= c * (e - f - (&3 / &5) * e pow 2 + e * f / &2) +
               s * (e + f - &11 / &10 + f pow 2 / &2 - (&3 / &5) * e * f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URCTT_PARALLEL_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  ABBREV_TAC `A = e - f - (&3 / &5) * e pow 2 + e * f / &2` THEN
  ABBREV_TAC `B = e + f - &11 / &10 + f pow 2 / &2 - (&3 / &5) * e * f` THEN
  SUBGOAL_THEN `e * A + f * B = &1 - (&3 / &5) * (e + f)` ASSUME_TAC THENL
  [EXPAND_TAC "A" THEN EXPAND_TAC "B" THEN
   UNDISCH_TAC `e pow 2 + f pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A + B` ASSUME_TAC THENL
  [EXPAND_TAC "A" THEN EXPAND_TAC "B" THEN
   SUBGOAL_THEN `&0 <= (e - &7 / &10) * (&1 - e) /\ e * f <= &1 / &2` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `e - f:real`]];
    ALL_TAC] THEN
   UNDISCH_TAC `e pow 2 + f pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= B` THENL
  [MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `e:real` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `e * ((c * A + s * B) - &0) = c * (e * A + f * B) + (e * s - f * c) * B`
   SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
   MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
   SUBGOAL_THEN `&0 < c * (A + B) /\ &0 <= (c - s) * --B` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC]);;

(* Lean: impossible *)
let URCTT_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cT sT uT vT aT.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     c977cc_normal cE sE /\ c977cc_normal cT sT /\ &1 < aE /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     ~linside cE sE uE vE aE (&3) (&12 / &5) /\
     ~linside cE sE uE vE aE (&7 / &2) (&3) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ABT_upper cE sE uE vE aE (--sT) cT <= vT
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cT sT`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URCRA_LOWER_FACE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal cE sE` THEN
   REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  URCTT_UNFOLD_TAC `linside cE sE uE vE aE (&3) (&3)` THEN
  URCTT_UNFOLD_TAC `linside cE sE uE vE aE (&16 / &5) (&3)` THEN
  URCTT_UNFOLD_TAC `linside cT sT uT vT aT (&12 / &5) (&3)` THEN
  SUBGOAL_THEN `&0 < cE * cT + sE * sT` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cE sE uE vE aE (--sT) cT =
     (sE * cT - cE * sT) * (uE + aE / &2) + (cE * cT + sE * sT) * (vE + aE / &2) +
     aE / &2 * (abs(sE * cT - cE * sT) + (cE * cT + sE * sT))` ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `uE + aE <= (&7 / &2) * cE + &3 * sE \/
                &3 * cE - (&7 / &2) * sE <= vE` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cE sE uE vE aE (&7 / &2) (&3)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `cE * sT - sE * cT <= &0` THENL
  [MP_TAC(SPECL [`cE:real`; `sE:real`; `cT:real`; `sT:real`] URCTT_SHALLOW_MARGIN) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN
    `&0 <= (sE * cT - cE * sT) * ((uE + aE) - (&3 * cE + &3 * sE)) /\
     &0 <= (cE * cT + sE * sT) * (vE - ((&12 / &5) * cE - &3 * sE)) /\
     &0 < (cE * cT + sE * sT) * (aE - &1)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `(sE * cT - cE * sT) * (&3 * cE + &3 * sE) +
     (cE * cT + sE * sT) * ((&12 / &5) * cE - &3 * sE + &1) -
     (&3 * cT - (&12 / &5) * sT) =
     cT * (cE - (&3 / &5) * cE pow 2) + sT * (sE - &3 / &5 - (&3 / &5) * cE * sE)`
   MP_TAC THENL
   [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `abs(sE * cT - cE * sT) = sE * cT - cE * sT` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC;
   SUBGOAL_THEN `abs(sE * cT - cE * sT) = cE * sT - sE * cT` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= cE * sT - sE * cT` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `cT:real`; `sT:real`] URCTT_STEEP_UPPER_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= (cE * sT - sE * cT) * (((&7 / &2) * cE + &3 * sE) - (uE + aE)) /\
      &0 <= (cE * cT + sE * sT) * (vE - ((&12 / &5) * cE - &3 * sE)) /\
      &0 < ((cE * cT + sE * sT) + (cE * sT - sE * cT)) * (aE - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(sE * cT - cE * sT) * ((&7 / &2) * cE + &3 * sE) +
      (cE * cT + sE * sT) * ((&12 / &5) * cE - &3 * sE) +
      ((cE * cT + sE * sT) + (cE * sT - sE * cT)) -
      (&3 * cT - (&12 / &5) * sT) =
      cT * (cE - sE - (&3 / &5) * cE pow 2 + cE * sE / &2) +
      sT * (cE + sE - &11 / &10 + sE pow 2 / &2 - (&3 / &5) * cE * sE)` MP_TAC THENL
    [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cE:real`; `sE:real`; `cT:real`; `sT:real`] URCTT_STEEP_LOWER_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= (cE * sT - sE * cT) * ((&3 * cE + &3 * sE) - uE) /\
      &0 <= (cE * cT + sE * sT) * (vE - (&3 * cE - (&7 / &2) * sE)) /\
      &0 < (cE * cT + sE * sT) * (aE - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(sE * cT - cE * sT) * (&3 * cE + &3 * sE) +
      (cE * cT + sE * sT) * (&3 * cE - (&7 / &2) * sE + &1) -
      (&3 * cT - (&12 / &5) * sT) =
      (cE * cT + sE * sT) * (&1 - sE / &2) - (&3 / &5) * sT` MP_TAC THENL
    [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]]);;
