(* ========================================================================= *)
(* Port of Compact/Geometry/DoubleAuxWallCoupling.lean                       *)
(*                                                                           *)
(* lower/upper are ABT_lower/ABT_upper, supportRadius tss_support_radius,    *)
(* pairRadius C977CB_pairRadius; the four-axis case split of the Lean proof  *)
(* (faceSeparation_of_disjoint + separated) is ABT_FOUR_AXES.                *)
(* pullSwap q = (s, c, u, --v - a, a); container_pullSwap is LCONT_PULLSW.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CentralWallEscape.ml";;
needs "n12/geometry/DoubleAuxWallMargins.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: faces (private) *)
let DAWC_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\
     linside c s u v a (&2) (&1543 / &500) /\
     linside c s u v a (&12 / &5) (&3) /\
     linside c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&2) (&113 / &50) /\
     ~linside c s u v a (&5 / &2) (&3)
     ==> (&8 / &5) * c + &3 * s <= u /\
         --(&5 / &2) * s + &3 * c <= v /\
         u < (&5 / &2) * c + &3 * s /\
         (&5 / &2) * c + &3 * s < u + a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `--(&2 / &5)` `&37 / &50`) THEN
  MP_TAC(WFP_SP `&1 / &2` `&37 / &50`) THEN
  MP_TAC(WFP_SP `&9 / &10` `&0`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(&8 / &5) * c + &3 * s <= u` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* apply a lemma instance: prove its antecedent from the assumptions, then
   add its conclusion as an assumption *)
let DAWC_STEP th (asl,w as g) =
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), REWRITE_TAC[lcont; ldisj] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[]) in
  ASSUME_TAC (MP th ath) g;;

(* Lean: missing_strong *)
let DAWC_MISSING_STRONG = prove
 (`forall cA sA uA vA aA cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ aA = aT /\ lcont cT sT uT vT aT /\
     &0 < cA /\ &0 <= sA /\ &4 * sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     &2 * cA + &2 * sA <= uA /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&8 / &5) (&3) /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> ~linside cA sA uA vA aA (&5 / &2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aT` o concl)) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aA:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aW:real = aA` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC)) THEN
  DAWC_STEP(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] DAWC_FACES) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  DAWC_STEP(REWRITE_RULE[lcont; LINSIDE_PULLSW]
    (SPECL [`sW:real`; `cW:real`; `uW:real`; `--vW - aA:real`; `aA:real`] CWE_RIGHT_WALL)) THEN
  NLIN_FACTS_TAC []
   [`sW * ((&8 / &5) * cW + &3 * sW) <= sW * uW`;
    `cW * (--(&5 / &2) * sW + &3 * cW) <= cW * vW`;
    `&0 < (aA - &1) * (cW + sW)`;
    `&0 < &1 + (&9 / &10) * cW * sW - cW - sW`] THEN
  DAWC_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`] DAWM_BOUNDS)) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cA sA uA vA aA (&2) (&113 / &50)`; `linside cA sA uA vA aA (&47 / &20) (&47 / &20)`;
    `linside cA sA uA vA aA (&5 / &2) (&3)`] THEN
  NLIN_FACTS_TAC [] [`&0 < cA * cW + sA * sW`] THEN
  SUBGOAL_THEN `ABT_lower cW sW uW vW aA (--sA) cA =
                (cA * sW - sA * cW) * uW + (cA * cW + sA * sW) * vW` ASSUME_TAC THENL
   [REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
    SUBGOAL_THEN `abs(--sA * cW + cA * sW) = cA * sW - sA * cW /\
                  abs(-- --sA * sW + cA * cW) = cA * cW + sA * sW`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x = y ==> abs x = y`) THEN
      CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cA sA uA vA aA (--sW) cW =
                --(cA * sW - sA * cW) * uA + (cA * cW + sA * sW) * (vA + aA)` ASSUME_TAC THENL
   [REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN
    SUBGOAL_THEN `abs(--sW * cA + cW * sA) = cA * sW - sA * cW /\
                  abs(-- --sW * sA + cW * cA) = cA * cW + sA * sW`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  (* minUpper *)
  SUBGOAL_THEN `cW * ((cA * sW - sA * cW) * uW + (cA * cW + sA * sW) * vW) =
                (cA * cW + sA * sW) * (sW * (uW + aA) + cW * (vW + aA)) - sA * uW -
                aA * (cA * cW + sA * sW) * (cW + sW)` ASSUME_TAC THENL
   [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`(cA * cW + sA * sW) * (sW * (uW + aA) + cW * (vW + aA)) <= (cA * cW + sA * sW) * &4`;
    `sA * ((&8 / &5) * cW + &3 * sW) <= sA * uW`;
    `&0 < (cA * cW + sA * sW) * (cW + sW)`;
    `(cA * cW + sA * sW) * (cW + sW) < aA * (cA * cW + sA * sW) * (cW + sW)`;
    `cW * ((cA * sW - sA * cW) * uW + (cA * cW + sA * sW) * vW) <=
     cW * (--(&5 / &2) * sA + &3 * cA)`] THEN
  SUBGOAL_THEN `(cA * sW - sA * cW) * uW + (cA * cW + sA * sW) * vW <=
                --(&5 / &2) * sA + &3 * cA` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_LMUL_EQ]; ALL_TAC] THEN
  (* maxLower *)
  SUBGOAL_THEN `--(cA * sW - sA * cW) * (&2 * cA + (&113 / &50) * sA) +
                (cA * cW + sA * sW) * (--(&5 / &2) * sA + &3 * cA) =
                --(&5 / &2) * sW + &3 * cW +
                (cA * sW - sA * cW) * ((&1 / &2) * cA + (&37 / &50) * sA)` ASSUME_TAC THENL
   [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`(cA * sW - sA * cW) * uA < (cA * sW - sA * cW) * (&2 * cA + (&113 / &50) * sA)`;
    `(cA * cW + sA * sW) * (--(&5 / &2) * sA + &3 * cA) < (cA * cW + sA * sW) * (vA + aA)`;
    `--(&5 / &2) * sW + &3 * cW +
     (cA * sW - sA * cW) * ((&1 / &2) * cA + (&37 / &50) * sA) <
     --(cA * sW - sA * cW) * uA + (cA * cW + sA * sW) * (vA + aA)`;
    `cW * vW <= cW * (--(&5 / &2) * sW + &3 * cW) + (&1 + (&9 / &10) * cW * sW - cW - sW)`;
    `cW * (--(&5 / &2) * sW + &3 * cW +
           (cA * sW - sA * cW) * ((&1 / &2) * cA + (&37 / &50) * sA)) <
     cW * (--(cA * sW - sA * cW) * uA + (cA * cW + sA * sW) * (vA + aA))`;
    `cW * vW < cW * (--(cA * sW - sA * cW) * uA + (cA * cW + sA * sW) * (vA + aA))`] THEN
  SUBGOAL_THEN `vW < --(cA * sW - sA * cW) * uA + (cA * cW + sA * sW) * (vA + aA)`
    ASSUME_TAC THENL [ASM_MESON_TAC[REAL_LT_LMUL_EQ]; ALL_TAC] THEN
  (* the A face at height 3 *)
  NLIN_FACTS_TAC [SQ_NONNEG `sA:real`]
   [`cA <= &1`; `uA < (&12 / &5) * cA + &3 * sA`; `(&12 / &5) * cA + &3 * sA < uA + aA`] THEN
  (* the four separating axes *)
  DAWC_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                   `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] ABT_FOUR_AXES) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  DAWC_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`;
     `&12 / &5`; `&3`; `cA:real`; `sA:real`] ABT_STRICT_BOUNDS)) THEN
  DAWC_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`;
     `&12 / &5`; `&3`; `--sA:real`; `cA:real`] ABT_STRICT_BOUNDS)) THEN
  DAWC_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
     `&5 / &2`; `&3`; `cW:real`; `sW:real`] ABT_STRICT_BOUNDS)) THEN
  DAWC_STEP(REWRITE_RULE[REAL_POW_2] (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
     `&5 / &2`; `&3`; `--sW:real`; `cW:real`] ABT_STRICT_BOUNDS)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_lower cW sW uW vW aA (--sA) cA =
                (cA * sW - sA * cW) * uW + (cA * cW + sA * sW) * vW`;
                ASSUME `ABT_upper cA sA uA vA aA (--sW) cW =
                --(cA * sW - sA * cW) * uA + (cA * cW + sA * sW) * (vA + aA)`]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  RASM_ARITH_TAC);;
