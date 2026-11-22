(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeBottomNextWall.lean                      *)
(*                                                                           *)
(* Bottom singleton O = (cO, sO, uO, vO, aO) with sO = --t, next wall        *)
(* D = (cD, sD, uD, vD, aD).  Normal is c977cc_normal; lower/upper are       *)
(* ABT_lower/ABT_upper.                                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C696BottomChainSelectors.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

(* apply a lemma instance: prove its antecedent from the assumptions, then
   add its conclusion as an assumption *)
let NBNW_STEP th (asl,w as g) =
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj; c977cc_normal]) THEN
     REWRITE_TAC[lcont; ldisj; c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[]) in
  ASSUME_TAC (MP th ath) g;;

(* Lean: entry (private) *)
let NBNW_ENTRY = prove
 (`forall d s. c977cc_normal d s ==> &0 <= (&1 - d) * (&1 - d / &2) + s * (d - &457 / &500)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&457 / &500 <= d` THENL
   [NLIN_TAC [];
    NLIN_FACTS_TAC [] [`&0 <= (d - s) * (&457 / &500 - d)`] THEN
    NLIN_TAC [SQ_NONNEG `d - &1207 / &1500`]]);;

(* Lean: shallow_cosine (private) *)
let NBNW_SHALLOW_COSINE = prove
 (`forall c t. c977cc_normal c t /\ t <= &1 / &5 ==> &19 / &20 < c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal c t` THEN REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN
  NLIN_TAC []);;

(* Lean: impossible *)
let NBNW_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD t.
     cO * cO + sO * sO = &1 /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cD sD /\ t <= &1 / &5 /\
     aO = aD /\ &1 < aO /\
     lcont cO sO uO vO aO /\ lcont cD sD uD vD aD /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&87 / &50) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     ~linside cD sD uD vD aD (&3) (&457 / &500) /\
     ldisj cO sO uO vO aO cD sD uD vD aD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aO:real = aD` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sO = --t` o concl)) THEN
  NBNW_STEP(SPECL [`cO:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  NBNW_STEP(SPECL [`cD:real`; `sD:real`] C977CC_NORMAL_BOUNDS) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  NBNW_STEP(SPECL [`cO:real`; `t:real`] NBNW_SHALLOW_COSINE) THEN
  NBNW_STEP(SPECL [`cD:real`; `sD:real`] NBNW_ENTRY) THEN
  NBNW_STEP(SPECL [`cO:real`; `--t:real`; `uO:real`; `vO:real`; `aO:real`; `t:real`]
    C977NCO_CORNER_FACE) THEN
  NBNW_STEP(SPECL [`cO:real`; `--t:real`; `uO:real`; `vO:real`; `aO:real`;
                   `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aO:real`] C696BCS_SINGLETON_WALL) THEN
  NBNW_STEP(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aO:real`] TSS_BOTTOM_WALL) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal; C696BCS_singletonStep]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cD sD uD vD aO (&2) (&457 / &500)`] THEN
  (* support forms *)
  NLIN_FACTS_TAC [] [`&0 <= cO * cD - t * sD`; `&0 <= cO * sD + t * cD`] THEN
  SUBGOAL_THEN `ABT_lower cD sD uD vD aO cO (--t) =
                (cO * cD - t * sD) * uD - (cO * sD + t * cD) * (vD + aO)` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cO * cD + --t * sD) = cO * cD - t * sD /\
                  abs(--cO * sD + --t * cD) = cO * sD + t * cD`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `--t:real`; `uO:real`; `vO:real`; `aO:real`; `t:real`;
                `cD:real`; `sD:real`] C977NCO_UPPER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= sD * uD + cD * vD` ASSUME_TAC THENL
   [UNDISCH_TAC `aO * (cD + abs sD) / &2 <= lcy cD sD uD vD aO` THEN
    REWRITE_TAC[lcy] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `uD + aO <= &3 * cD + (&457 / &500) * sD \/
                (&457 / &500) * cD - &3 * sD <= vD` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside cD sD uD vD aO (&3) (&457 / &500)`) THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  (* noD *)
  SUBGOAL_THEN `cO * ((cD * cO - sD * t) * (uO + aO) + (cD * t + sD * cO) * (vO + aO) -
                      (&2 * cD + (&457 / &500) * sD)) =
                cD * (uO - (cO - t)) + (cO * sD + t * cD) * (cO * vO - t * (uO + aO)) +
                (aO - &1) * (cD + cO * (cO * sD + t * cD)) + cD * (&1 - cO) * (&1 - t) +
                cO * sD * (cO - &457 / &500)` ASSUME_TAC THENL
   [UNDISCH_TAC `cO pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cD * (uO - (cO - t))`;
    `&0 <= (cO * sD + t * cD) * (cO * vO - t * (uO + aO))`;
    `&0 < cD + cO * (cO * sD + t * cD)`;
    `&0 < (aO - &1) * (cD + cO * (cO * sD + t * cD))`;
    `&0 <= cD * (&1 - cO)`; `&0 <= cD * (&1 - cO) * (&1 - t)`;
    `&0 <= cO * sD`; `&0 <= cO * sD * (cO - &457 / &500)`;
    `&0 < cO * ((cD * cO - sD * t) * (uO + aO) + (cD * t + sD * cO) * (vO + aO) -
               (&2 * cD + (&457 / &500) * sD))`;
    `&2 * cD + (&457 / &500) * sD <
     (cD * cO - sD * t) * (uO + aO) + (cD * t + sD * cO) * (vO + aO)`] THEN
  (* noO *)
  SUBGOAL_THEN `(cO * cD - t * sD) * uD - (cO * sD + t * cD) * (vD + aO) < uO + aO`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `&457 / &500 * cD - &3 * sD`)) (concl th))) THENL
     [SUBGOAL_THEN `cD * (uO + aO - ((cO * cD - t * sD) * uD - (cO * sD + t * cD) * (vD + aO))) =
          cD * (uO - (cO - t)) + cO * (&3 * cD + (&457 / &500) * sD - (uD + aO)) +
          (cO * sD + t * cD) * (sD * uD + cD * vD) +
          (aO - &1) * (cD + cO + cD * (cO * sD + t * cD)) +
          (cO * ((&1 - cD) * (&1 - cD / &2) + sD * (cD - &457 / &500)) +
           cD * (&1 - cO) + (cO / &2 - t) * cD * (&1 - cD))` ASSUME_TAC THENL
       [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      NLIN_FACTS_TAC []
       [`&0 <= cO * ((&1 - cD) * (&1 - cD / &2) + sD * (cD - &457 / &500))`;
        `&0 <= (cO / &2 - t) * cD`; `&0 <= (cO / &2 - t) * cD * (&1 - cD)`;
        `&0 <= cO * (&3 * cD + (&457 / &500) * sD - (uD + aO))`;
        `&0 <= (cO * sD + t * cD) * (sD * uD + cD * vD)`;
        `&0 < cD + cO + cD * (cO * sD + t * cD)`;
        `&0 < (aO - &1) * (cD + cO + cD * (cO * sD + t * cD))`;
        `&0 < cD * (uO + aO - ((cO * cD - t * sD) * uD - (cO * sD + t * cD) * (vD + aO)))`] THEN
      NLIN_TAC [];
      SUBGOAL_THEN `uO + aO - ((cO * cD - t * sD) * uD - (cO * sD + t * cD) * (vD + aO)) =
          (uO - (cO - t)) + (cO * cD - t * sD) * (&2 * cD + (&457 / &500) * sD - uD) +
          (cO * sD + t * cD) * (vD - ((&457 / &500) * cD - &3 * sD)) +
          (aO - &1) * (&1 + (cO * sD + t * cD)) +
          (&1 - cO * (&1 + sD pow 2 - sD) - t * (cD * sD - cD + &43 / &500))` ASSUME_TAC THENL
       [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      NLIN_FACTS_TAC []
       [`&0 <= sD * (&1 - sD)`; `sD <= &3 / &4`; `cD * sD - cD + &43 / &500 <= &0`;
        `&0 <= cO * sD * (&1 - sD)`; `&0 <= t * --(cD * sD - cD + &43 / &500)`;
        `&0 <= &1 - cO * (&1 + sD pow 2 - sD) - t * (cD * sD - cD + &43 / &500)`;
        `&0 <= (cO * cD - t * sD) * (&2 * cD + (&457 / &500) * sD - uD)`;
        `&0 <= (cO * sD + t * cD) * (vD - ((&457 / &500) * cD - &3 * sD))`;
        `&0 < (aO - &1) * (&1 + (cO * sD + t * cD))`] THEN
      RASM_ARITH_TAC];
    ALL_TAC] THEN
  (* the directed separation *)
  NBNW_STEP(SPECL [`cO:real`; `--t:real`; `uO:real`; `vO:real`; `aO:real`] ABT_OWNU) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  NBNW_STEP(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aO:real`] ABT_OWNU) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_upper cO (--t) uO vO aO cO (--t) = uO + aO`;
     ASSUME `ABT_lower cD sD uD vD aO cD sD = uD`;
     ASSUME `ABT_lower cD sD uD vD aO cO (--t) =
             (cO * cD - t * sD) * uD - (cO * sD + t * cD) * (vD + aO)`;
     ASSUME `ABT_upper cO (--t) uO vO aO cD sD =
             (cD * cO - sD * t) * (uO + aO) + (cD * t + sD * cO) * (vO + aO)`]) THEN
  FIRST_X_ASSUM(fun th -> if can (find_term ((=) `&43 / &130`)) (concl th)
    then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  STRIP_TAC THEN RASM_ARITH_TAC);;
