(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallRightSupport.lean                     *)
(*                                                                           *)
(* Central square A = (cA, sA, uA, vA, aA), right neighbour R.  Normal is    *)
(* c977cc_normal; lower/upper are ABT_lower/ABT_upper.  The two conclusions  *)
(* of the Lean theorems are written out with e = uA - 2 (cA + sA).           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/SectionCapacity.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FullAuxWallRightAxes.ml";;
needs "n12/geometry/FullAuxWallEscape.ml";;
needs "n12/geometry/CentralOuterReach.ml";;

let FAWRS_STEP th (asl,w as g) =
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj; c977cc_normal]) THEN
     REWRITE_TAC[lcont; ldisj; c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[]) in
  ASSUME_TAC (MP th ath) g;;

let FAWRS_STRIP_TAC =
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC));;

(* Lean: upper_corner_wall (private) *)
let FAWRS_UPPER_CORNER_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ lcont c s u v a
     ==> c * (u + a) - s * (v + a) <= &4`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcont] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &4 - c * (u + a) + s * (v + a) ==> c * (u + a) - s * (v + a) <= &4`) THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `c - s:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + a - e) - s * (v + a - e)`;
                                `s * (u + a - e) + c * (v + a - e)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[linside] THEN
    SUBGOAL_THEN `c * (c * (u + a - e) - s * (v + a - e)) + s * (s * (u + a - e) + c * (v + a - e)) =
                  u + a - e /\
                  --s * (c * (u + a - e) - s * (v + a - e)) + c * (s * (u + a - e) + c * (v + a - e)) =
                  v + a - e` (fun th -> REWRITE_TAC[th] THEN ASM_REAL_ARITH_TAC) THEN
    CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
    REAL_ARITH_TAC]);;

(* Lean: positive_below (private) *)
let FAWRS_POSITIVE_BELOW = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cA sA /\ c977cc_normal cR sR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     cA * sR <= sA * cR /\
     (uA + aA <= ABT_lower cR sR uR vR aR cA sA \/ ABT_upper cA sA uA vA aA cR sR <= uR)
     ==> uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2 /\
         cA * (uA - &2 * (cA + sA)) + (&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA) < &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWRS_STEP(SPECL [`cR:real`; `sR:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `cR:real`; `sR:real`] C977CSB_SINE_ORDER) THEN
  FAWRS_STEP(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CWE_RIGHT_WALL) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `cR:real`; `sR:real`] FAWRM_POSITIVE_U_MARGIN) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `cR:real`; `sR:real`] FAWRM_MARGIN) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `cR:real`; `sR:real`] FAWRM_BASELINE_MARGIN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWRS_STRIP_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cR sR uR vR aA (&1543 / &500) (&2)`] THEN
  NLIN_FACTS_TAC [] [`&0 < cA * cR + sA * sR`] THEN
  SUBGOAL_THEN `ABT_lower cR sR uR vR aA cA sA =
                (cA * cR + sA * sR) * uR - (cA * sR - sA * cR) * vR` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cA * cR + sA * sR) = cA * cR + sA * sR /\
                  abs(--cA * sR + sA * cR) = --(cA * sR - sA * cR)`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cA sA uA vA aA cR sR =
                (cA * cR + sA * sR) * (uA + aA) + (cA * sR - sA * cR) * vA` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cR * cA + sR * sA) = cA * cR + sA * sR /\
                  abs(--cR * sA + sR * cA) = --(cA * sR - sA * cR)`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_lower cR sR uR vR aA cA sA =
                (cA * cR + sA * sR) * uR - (cA * sR - sA * cR) * vR`;
                ASSUME `ABT_upper cA sA uA vA aA cR sR =
                (cA * cR + sA * sR) * (uA + aA) + (cA * sR - sA * cR) * vA`]) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* the central square below R along its own normal *)
    SUBGOAL_THEN `cR * ((cA * cR + sA * sR) * uR - (cA * sR - sA * cR) * vR) =
                  (cA * cR + sA * sR) * (cR * (uR + aA) - sR * vR) + sA * vR -
                  aA * cR * (cA * cR + sA * sR)` ASSUME_TAC THENL
     [UNDISCH_TAC `cR pow 2 + sR pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`(cA * cR + sA * sR) * (cR * (uR + aA) - sR * vR) <= (cA * cR + sA * sR) * &4`;
      `sA * vR <= sA * (--sR * (&1543 / &500) + cR * &2)`;
      `cR * (uA + aA) <= cR * ((cA * cR + sA * sR) * uR - (cA * sR - sA * cR) * vR)`;
      `&0 <= cR * (uA - &2 * (cA + sA))`;
      `&0 < cR * (&1 + (cA * cR + sA * sR))`;
      `&0 < (aA - &1) * (cR * (&1 + (cA * cR + sA * sR)))`] THEN
    RASM_ARITH_TAC;
    (* R beyond the central square along R's normal *)
    SUBGOAL_THEN `(cA * cR + sA * sR) * (&2 * (cA + sA)) + (cA * sR - sA * cR) * (&3 * cA - (&12 / &5) * sA) =
                  cR * (&2 + (&2 / &5) * sA pow 2 - cA * sA) +
                  sR * (&3 - sA pow 2 - (&2 / &5) * cA * sA)` ASSUME_TAC THENL
     [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `cR * (cA * cR + sA * sR) - cA = --(sR * (cA * sR - sA * cR))` ASSUME_TAC THENL
     [UNDISCH_TAC `cR pow 2 + sR pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= --(cA * sR - sA * cR) * (&3 * cA - (&12 / &5) * sA - (vA + aA))`;
      `cR * (&2 + (&2 / &5) * sA pow 2 - cA * sA) + sR * (&3 - sA pow 2 - (&2 / &5) * cA * sA) +
       (cA * cR + sA * sR) * (uA - &2 * (cA + sA)) +
       aA * ((cA * cR + sA * sR) - (cA * sR - sA * cR)) <=
       (cA * cR + sA * sR) * (uA + aA) + (cA * sR - sA * cR) * vA`;
      `sR * vR <= sR * (--sR * (&1543 / &500) + cR * &2)`;
      `cR * uR + aA * cR + (&1543 / &500) * sR pow 2 - &2 * cR * sR <= &4`;
      `cR * (cR * (&2 + (&2 / &5) * sA pow 2 - cA * sA) + sR * (&3 - sA pow 2 - (&2 / &5) * cA * sA) +
       (cA * cR + sA * sR) * (uA - &2 * (cA + sA)) +
       aA * ((cA * cR + sA * sR) - (cA * sR - sA * cR))) <= cR * uR`;
      `cR * (cA * cR + sA * sR) * (uA - &2 * (cA + sA)) +
       (cR pow 2 * (&2 + (&2 / &5) * sA pow 2 - cA * sA) +
        cR * sR * (&1 - sA pow 2 - (&2 / &5) * cA * sA) +
        cR * ((cA * cR + sA * sR) - (cA * sR - sA * cR) + &1) + (&1543 / &500) * sR pow 2 - &4) +
       (aA - &1) * cR * ((cA * cR + sA * sR) - (cA * sR - sA * cR) + &1) <= &0`;
      `&0 < cR * ((cA * cR + sA * sR) - (cA * sR - sA * cR) + &1)`;
      `&0 < (aA - &1) * (cR * ((cA * cR + sA * sR) - (cA * sR - sA * cR) + &1))`] THEN
    SUBGOAL_THEN `uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      NLIN_FACTS_TAC []
       [`&0 < cR * (cA * cR + sA * sR)`;
        `&0 <= (cR * (cA * cR + sA * sR)) * ((uA - &2 * (cA + sA)) - (&1 / &5) * sA pow 2)`] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    NLIN_FACTS_TAC []
     [`sR * (cA * sR - sA * cR) <= &0`;
      `&0 <= (cR * (cA * cR + sA * sR) - cA) * (uA - &2 * (cA + sA))`] THEN
    RASM_ARITH_TAC]);;

(* Lean: negative (private) *)
let FAWRS_NEGATIVE = prove
 (`forall cA sA uA vA aA cR sR uR vR aR t.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cA sA /\ c977cc_normal cR t /\ sR = --t /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     (uA + aA <= ABT_lower cR sR uR vR aR cA sA \/ ABT_upper cA sA uA vA aA cR sR <= uR)
     ==> uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2 /\
         cA * (uA - &2 * (cA + sA)) + (&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA) < &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sR = --t` o concl)) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWRS_STEP(SPECL [`cR:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`] FAWRM_CENTRAL_BOUNDS) THEN
  FAWRS_STEP(SPECL [`cR:real`; `--t:real`; `uR:real`; `vR:real`; `aA:real`] FAWRS_UPPER_CORNER_WALL) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `cR:real`; `t:real`] FAWRM_NEGATIVE_U_MARGIN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWRS_STRIP_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cR (--t) uR vR aA (&1543 / &500) (&2)`; `linside cR (--t) uR vR aA (&3) (&12 / &5)`] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cA * t + sA * cR`; `(&7 / &10) * cR <= cA * cR - sA * t`; `&0 < cA * cR - sA * t`] THEN
  SUBGOAL_THEN `ABT_lower cR (--t) uR vR aA cA sA =
                (cA * cR - sA * t) * uR + (cA * t + sA * cR) * vR` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cA * cR + sA * --t) = cA * cR - sA * t /\
                  abs(--cA * --t + sA * cR) = cA * t + sA * cR`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cA sA uA vA aA cR (--t) =
                (cA * cR - sA * t) * (uA + aA) - (cA * t + sA * cR) * vA` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cR * cA + --t * sA) = cA * cR - sA * t /\
                  abs(--cR * sA + --t * cA) = cA * t + sA * cR`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_lower cR (--t) uR vR aA cA sA =
                (cA * cR - sA * t) * uR + (cA * t + sA * cR) * vR`;
                ASSUME `ABT_upper cA sA uA vA aA cR (--t) =
                (cA * cR - sA * t) * (uA + aA) - (cA * t + sA * cR) * vA`]) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN `cR * ((cA * cR - sA * t) * uR + (cA * t + sA * cR) * vR) =
                  (cA * cR - sA * t) * (cR * (uR + aA) + t * (vR + aA)) + sA * vR -
                  aA * (cA * cR - sA * t) * (cR + t)` ASSUME_TAC THENL
     [UNDISCH_TAC `cR pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`(cA * cR - sA * t) * (cR * (uR + aA) + t * (vR + aA)) <= (cA * cR - sA * t) * &4`;
      `sA * vR <= sA * (-- --t * (&1543 / &500) + cR * &2)`;
      `cR * (uA + aA) <= cR * ((cA * cR - sA * t) * uR + (cA * t + sA * cR) * vR)`;
      `&0 <= cR * (uA - &2 * (cA + sA))`;
      `&0 < cR + (cA * cR - sA * t) * (cR + t)`;
      `&0 < (aA - &1) * (cR + (cA * cR - sA * t) * (cR + t))`] THEN
    RASM_ARITH_TAC;
    NLIN_FACTS_TAC []
     [`&0 <= (cA * t + sA * cR) * (&3 * cA - (&12 / &5) * sA - (vA + aA))`;
      `&0 <= cR * ((&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA) + (&3 / &25) * sA pow 2)`;
      `&0 <= t * (cA - sA - &3 / &5 + sA pow 2 + (&2 / &5) * cA * sA)`;
      `&0 < (aA - &1) * ((cA * cR - sA * t) + (cA * t + sA * cR))`] THEN
    SUBGOAL_THEN `(cA * cR - sA * t) * (uA - &2 * (cA + sA)) +
                  cR * ((&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA)) +
                  t * (cA - sA - &3 / &5 + sA pow 2 + (&2 / &5) * cA * sA) +
                  (aA - &1) * ((cA * cR - sA * t) + (cA * t + sA * cR)) < &0` ASSUME_TAC THENL
     [SUBGOAL_THEN `(cA * cR - sA * t) * (&2 * (cA + sA)) - (cA * t + sA * cR) * (&3 * cA - (&12 / &5) * sA) =
                    cR * (&2 + (&2 / &5) * sA pow 2 - cA * sA) - t * (&3 - sA pow 2 - (&2 / &5) * cA * sA)`
        ASSUME_TAC THENL
       [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      NLIN_FACTS_TAC []
       [`&0 <= (cA * cR - sA * t) * ((uA - &2 * (cA + sA)) - (&1 / &5) * sA pow 2)`;
        `&0 <= sA pow 2 * ((cA * cR - sA * t) - (&7 / &10) * cR)`;
        `&0 <= cR * sA pow 2`] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    NLIN_FACTS_TAC []
     [`sA pow 2 <= &1 / &16`; `uA - &2 * (cA + sA) <= &1 / &80`;
      `&0 <= uA - &2 * (cA + sA)`;
      `sA * (uA - &2 * (cA + sA)) <= &1 / &320`;
      `&0 <= t * ((cA - sA - &3 / &5 + sA pow 2 + (&2 / &5) * cA * sA) - sA * (uA - &2 * (cA + sA)))`;
      `cR * (cA * (uA - &2 * (cA + sA)) + (&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA)) < &0`] THEN
    NLIN_TAC []]);;

let FAWRS_FINISH_TAC = FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_ASSUM CONTR_TAC;;

(* Lean: canonical_bounds *)
let FAWRS_CANONICAL_BOUNDS = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cA sA /\ &0 < cR /\ --cR <= sR /\ sR <= cR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     --(&47 / &20) * sA + (&33 / &20) * cA <= vA /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     linside cA sA uA vA aA (&47 / &20) (&53 / &20) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2 /\
         cA * (uA - &2 * (cA + sA)) + (&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`] C977CC_NORMAL_BOUNDS) THEN
  FAWRS_STRIP_TAC THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                    `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] FAWRA_ALTERNATIVES) THEN
  ASM_CASES_TAC `&0 <= sR` THENL
   [ASM_CASES_TAC `&0 <= cA * sR - sA * cR` THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                          `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
          CWPS_CENTRAL_AXIS_IMPOSSIBLE);
        FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                          `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
          CWPS_WALL_AXIS_IMPOSSIBLE)] THEN
      FAWRS_FINISH_TAC;
      FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] FAWRS_POSITIVE_BELOW) THEN
      FAWRS_FINISH_TAC];
    FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`; `--sR:real`] FAWRS_NEGATIVE) THEN
    FAWRS_FINISH_TAC]);;

(* Lean: canonical *)
let FAWRS_CANONICAL = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cA sA /\ &0 < cR /\ --cR <= sR /\ sR <= cR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     --(&47 / &20) * sA + (&33 / &20) * cA <= vA /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     linside cA sA uA vA aA (&47 / &20) (&53 / &20) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2`,
  MESON_TAC[FAWRS_CANONICAL_BOUNDS]);;

(* Lean: quadratic_of_clearance *)
let FAWRS_QUADRATIC_OF_CLEARANCE = prove
 (`forall c s e. c977cc_normal c s /\ &4 * s <= c /\
     c * e + (&2 / &5) * s pow 2 - (&1 - c) * (&1 - s) < &0
     ==> e < s pow 2 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWRS_STRIP_TAC THEN
  SUBGOAL_THEN `((&2 / &5) + (&1 / &10) * c) * (&1 + c) - (&1 - s) =
                s - (&1 / &10) * s pow 2 - (&1 / &2) * (&1 - c) /\
                (&1 / &10) * c * s pow 2 + (&2 / &5) * s pow 2 - (&1 - c) * (&1 - s) =
                (&1 - c) * (((&2 / &5) + (&1 / &10) * c) * (&1 + c) - (&1 - s))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`s <= &1 / &4`; `&0 <= c * (&1 - c)`; `&1 - c <= s pow 2`;
    `&0 <= s * (&1 - (&3 / &5) * s)`;
    `&0 <= ((&2 / &5) + (&1 / &10) * c) * (&1 + c) - (&1 - s)`;
    `&0 <= (&1 - c) * (((&2 / &5) + (&1 / &10) * c) * (&1 + c) - (&1 - s))`;
    `c * e < c * (s pow 2 / &10)`] THEN
  ASM_MESON_TAC[REAL_LT_LMUL_EQ; REAL_ARITH `&7 / &10 <= c ==> &0 < c`]);;

(* Lean: bounds *)
let FAWRS_BOUNDS = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cA sA /\ &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     --(&47 / &20) * sA + (&33 / &20) * cA <= vA /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     linside cA sA uA vA aA (&47 / &20) (&53 / &20) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2 /\
         cA * (uA - &2 * (cA + sA)) + (&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = aA` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj; lcont]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC)) THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                    `cr:real`; `sr:real`; `ur:real`; `vr:real`; `aA:real`] FAWRS_CANONICAL_BOUNDS) THEN
  FAWRS_FINISH_TAC);;

(* Lean: excess *)
let FAWRS_EXCESS = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cA sA /\ &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     --(&47 / &20) * sA + (&33 / &20) * cA <= vA /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     linside cA sA uA vA aA (&47 / &20) (&53 / &20) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2`,
  MESON_TAC[FAWRS_BOUNDS]);;

(* Lean: original_bounds_of_missing *)
let FAWRS_ORIGINAL_BOUNDS_OF_MISSING = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ~linside cA sA uA vA aA (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2 /\
         cA * (uA - &2 * (cA + sA)) + (&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                    `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] FAWE_NARROW_FACES_OF_MISSING) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CWPA_CENTRAL_LOWER_FACES) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] COR_POINTS) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                    `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] FAWRS_BOUNDS) THEN
  FAWRS_FINISH_TAC);;

(* Lean: original_bounds *)
let FAWRS_ORIGINAL_BOUNDS = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2 /\
         cA * (uA - &2 * (cA + sA)) + (&2 / &5) * sA pow 2 - (&1 - cA) * (&1 - sA) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWRS_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                    `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] FAWRS_ORIGINAL_BOUNDS_OF_MISSING) THEN
  FAWRS_FINISH_TAC);;

(* Lean: from_original *)
let FAWRS_FROM_ORIGINAL = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> uA - &2 * (cA + sA) < (&1 / &5) * sA pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FAWRS_ORIGINAL_BOUNDS) THEN MESON_TAC[]);;
