(* ========================================================================= *)
(* Port of Compact/Geometry/C868CentralSupport.lean (Jatloe, N12-jatloe).     *)
(* The lower-left square's missing auxiliary points constrain its support.   *)
(* Normal: c977cc_normal; upper: ABT_upper; upper_in_bands:                  *)
(* C977NCO_UPPER_IN_BANDS; short_projections: WFP_SP;                        *)
(* C868CentralMargins.modeI..III_nonneg/nonpos: C868CM_MODE*.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/C868CentralMargins.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: modes *)
let C868CS_MODES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ &0 <= s /\ s <= c /\ &1 < a /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&8 / &5) (&1) /\
     ~linside c s u v a (&1) (&8 / &5)
     ==> (&8 / &5) * c + s <= u \/
         ((&8 / &5) * c - s <= v /\ &13 * s < c) \/
         (c + (&8 / &5) * s <= u /\ c - (&8 / &5) * s <= v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&3 / &5` `&3 / &5`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `c * &8 / &5 + s * &1 <= u` THENL
  [DISJ1_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c - (&8 / &5) * s <= v` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c * &1 + s * &8 / &5 <= u` THENL
  [DISJ2_TAC THEN DISJ2_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: positive_support *)
let C868CS_POSITIVE_SUPPORT = prove
 (`forall cA sA uA vA aA c s.
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal c s /\ c977cc_normal cA sA /\ &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5)
     ==> (&33 / &20) * c + (&47 / &20) * s < ABT_upper cA sA uA vA aA c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let mode th = MP_TAC(SPECL [`c:real`; `s:real`; `cA:real`; `sA:real`] th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC in
  let prod tm = SUBGOAL_THEN tm ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] in
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cA sA`)) THEN
  MP_TAC(ASSUME `c977cc_normal c s`) THEN MP_TAC(ASSUME `c977cc_normal cA sA`) THEN
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    C868CS_MODES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `&2`; `&87 / &50`; `c:real`; `s:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c * cA + s * sA` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  prod `&0 < (c * cA + s * sA) * (aA - &1)` THEN
  UNDISCH_TAC `linside cA sA uA vA aA (&2) (&87 / &50)` THEN
  UNDISCH_TAC `linside cA sA uA vA aA (&87 / &50) (&2)` THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(c * cA + s * sA) = c * cA + s * sA` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s * cA - c * sA` THENL
  [SUBGOAL_THEN `abs(--c * sA + s * cA) = s * cA - c * sA` SUBST1_TAC THENL
   [REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   prod `&0 <= (s * cA - c * sA) * (aA - &1)` THEN
   FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THENL
   [prod `&0 <= (c * cA + s * sA) * (uA - (&8 / &5 * cA + sA))` THEN
    prod `&0 <= (s * cA - c * sA) * ((vA + aA) - (&2 * cA - &87 / &50 * sA))` THEN
    mode C868CM_MODEI_NONNEG THEN RASM_ARITH_TAC;
    prod `&0 < (c * cA + s * sA) * ((uA + aA) - (&2 * cA + &87 / &50 * sA))` THEN
    prod `&0 <= (s * cA - c * sA) * (vA - (&8 / &5 * cA - sA))` THEN
    SUBGOAL_THEN `&13 * sA <= cA` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    mode C868CM_MODEII_NONNEG THEN RASM_ARITH_TAC;
    prod `&0 <= (c * cA + s * sA) * (uA - (cA + &8 / &5 * sA))` THEN
    prod `&0 <= (s * cA - c * sA) * (vA - (cA - &8 / &5 * sA))` THEN
    mode C868CM_MODEIII_NONNEG THEN RASM_ARITH_TAC];
   SUBGOAL_THEN `s * cA - c * sA <= &0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(--c * sA + s * cA) = --(s * cA - c * sA)` SUBST1_TAC THENL
   [REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   prod `&0 <= --(s * cA - c * sA) * ((&87 / &50 * cA - &2 * sA) - vA)` THEN
   FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THENL
   [prod `&0 <= (c * cA + s * sA) * (uA - (&8 / &5 * cA + sA))` THEN
    mode C868CM_MODEI_NONPOS THEN RASM_ARITH_TAC;
    prod `&0 <= c * (cA - &13 * sA)` THEN
    SUBGOAL_THEN `(&13 * s) * cA <= c * cA` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&13 * s <= c` ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `~(c < x) ==> x <= c`) THEN DISCH_TAC THEN
     SUBGOAL_THEN `c * cA < (&13 * s) * cA` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN
    UNDISCH_TAC `c * &2 + s * &87 / &50 < ABT_upper cA sA uA vA aA c s` THEN
    REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(c * cA + s * sA) = c * cA + s * sA /\
                  abs(--c * sA + s * cA) = --(s * cA - c * sA)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[real_abs] THEN CONJ_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    prod `&0 <= (c * cA + s * sA) * (uA - (cA + &8 / &5 * sA))` THEN
    mode C868CM_MODEIII_NONPOS THEN RASM_ARITH_TAC]]);;
