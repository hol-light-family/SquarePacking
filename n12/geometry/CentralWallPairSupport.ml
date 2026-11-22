(* ========================================================================= *)
(* Port of Compact/Geometry/CentralWallPairSupport.lean (Jatloe).             *)
(* The two remaining longitudinal separators contradict the full square    *)
(* supports and the actual right wall.                                      *)
(* d = cA*cR + sA*sR and k = cA*sR - sA*cR are written out.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralWallPairAxes.ml";;
needs "n12/geometry/CentralWallParallelMargin.ml";;

(* Lean: support_formulas *)
let CWPS_SUPPORT_FORMULAS = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     &0 <= cA * cR + sA * sR /\ &0 <= cA * sR - sA * cR
     ==> ABT_upper cA sA uA vA aA cR sR =
           (cA * cR + sA * sR) * (uA + aA) + (cA * sR - sA * cR) * (vA + aA) /\
         ABT_lower cR sR uR vR aR cA sA =
           (cA * cR + sA * sR) * uR - (cA * sR - sA * cR) * (vR + aR)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_upper; ABT_lower; tss_support_radius; lcx; lcy] THEN
  SUBGOAL_THEN `abs(cR * cA + sR * sA) = cA * cR + sA * sR /\
                abs(--cR * sA + sR * cA) = cA * sR - sA * cR /\
                abs(cA * cR + sA * sR) = cA * cR + sA * sR /\
                abs(--cA * sR + sA * cR) = cA * sR - sA * cR`
  (fun th -> REWRITE_TAC[th]) THENL
  [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN REAL_ARITH_TAC);;

(* Lean: shallow_wall_of_central_axis *)
let CWPS_SHALLOW_WALL_OF_CENTRAL_AXIS = prove
 (`forall cA sA uA (vA:real) aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ &0 < cA /\ &0 <= sA /\ &0 < cR /\ &0 <= sR /\
     &12 * sA <= &5 * cA /\ &0 <= cA * sR - sA * cR /\
     &2 * cA + &2 * sA <= uA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     uA + aA <= ABT_lower cR sR uR vR aR cA sA
     ==> sR < cR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cA * cR + sA * sR` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
    CWPS_SUPPORT_FORMULAS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  CWPA_UNFOLD_TAC `linside cR sR uR vR aR (&1543 / &500) (&2)` THEN
  CWPA_UNFOLD_TAC `linside cR sR uR vR aR (&3) (&12 / &5)` THEN
  SUBGOAL_THEN `cA <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `sA:real`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cA * cR + sA * sR) * uR <
      (cA * cR + sA * sR) * (cR * &1543 / &500 + sR * &2) /\
    (cA * sR - sA * cR) * (--sR * &3 + cR * &12 / &5) <=
      (cA * sR - sA * cR) * (vR + aR) /\
    &0 <= cR * ((sR - cR) * ((&2 / &5) * cA - (&43 / &500) * sA) +
                cR * ((&157 / &500) * cA - (&243 / &500) * sA))`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cA * cR + sA * sR) * (cR * &1543 / &500 + sR * &2) -
    (cA * sR - sA * cR) * (--sR * &3 + cR * &12 / &5) =
      (&1543 / &500) * cA + &2 * sA -
      (cA * sR - sA * cR) * ((&2 / &5) * cR + (&43 / &500) * sR) /\
    (cA * sR - sA * cR) * ((&2 / &5) * cR + (&43 / &500) * sR) -
      (&43 / &500) * cA =
    cR * ((sR - cR) * ((&2 / &5) * cA - (&43 / &500) * sA) +
          cR * ((&157 / &500) * cA - (&243 / &500) * sA))`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: central_axis_impossible *)
let CWPS_CENTRAL_AXIS_IMPOSSIBLE = prove
 (`forall cA sA uA (vA:real) aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ &0 < cR /\ &0 <= sR /\
     &12 * sA <= &5 * cA /\ &0 <= cA * sR - sA * cR /\
     &2 * cA + &2 * sA <= uA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     uA + aA <= ABT_lower cR sR uR vR aR cA sA
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
    CWPS_SHALLOW_WALL_OF_CENTRAL_AXIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < cA * cR + sA * sR` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
    CWPS_SUPPORT_FORMULAS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
    CWE_RIGHT_WALL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CWPA_UNFOLD_TAC `linside cR sR uR vR aR (&1543 / &500) (&2)` THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cR:real`; `sR:real`] CWPM_PARALLEL_MARGIN) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
   DISCH_TAC] THEN
  SUBGOAL_THEN
   `(cA * cR + sA * sR) * (cR * (uR + aR) - sR * vR) <= (cA * cR + sA * sR) * &4 /\
    sA * vR <= sA * (--sR * &1543 / &500 + cR * &2) /\
    &0 <= cR * (&1 + (cA - sA) * cR + (cA + sA) * sR - &2 * cA -
                (&457 / &500) * sA * (sR / cR)) /\
    cR * (uA + aA) <= cR * ((cA * cR + sA * sR) * uR - (cA * sR - sA * cR) * (vR + aR)) /\
    cR * (&2 * cA + &2 * sA) <= cR * uA /\
    &0 < (aA - &1) * (cR * (&1 + (cA * cR + sA * sR) + (cA * sR - sA * cR)))`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `((cA * cR + sA * sR) * sR - cR * (cA * sR - sA * cR)) * vR = sA * vR /\
    (&457 / &500) * sA * (cR * (sR / cR)) = (&457 / &500) * sA * sR`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `&0 < cR` THEN CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aR`)) THEN
  RASM_ARITH_TAC);;

(* Lean: wall_axis_impossible *)
let CWPS_WALL_AXIS_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ &0 < cR /\ &0 <= sR /\
     &12 * sA <= &5 * cA /\ &0 <= cA * sR - sA * cR /\
     &2 * cA + &2 * sA <= uA /\
     --(&47 / &20) * sA + (&33 / &20) * cA <= vA /\
     linside cA sA uA vA aA (&47 / &20) (&53 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     ABT_upper cA sA uA vA aA cR sR <= uR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  SUBGOAL_THEN `&0 < cA * cR + sA * sR` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    CWPS_SUPPORT_FORMULAS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    CWE_RIGHT_WALL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CWPA_UNFOLD_TAC `linside cR sR uR vR aA (&1543 / &500) (&2)` THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `&47 / &20`; `&53 / &20`; `cR:real`; `sR:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&13 / &20) * sR < (&92 / &125) * cR` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists p q w. p * cA = sA /\ q * cR = sR /\ w * cR = &1`
  STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXISTS_TAC [`sA / cA`; `sR / cR`; `&1 / cR`] THEN
   UNDISCH_TAC `&0 < cA` THEN UNDISCH_TAC `&0 < cR` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p /\ p <= q /\ &0 <= q /\ q <= &23 / &20 /\ &0 < w`
  STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `(q - p) * (cA * cR) = cA * sR - sA * cR /\ &0 < cA * cR`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [UNDISCH_TAC `p * cA = sA` THEN UNDISCH_TAC `q * cR = sR` THEN
     CONV_TAC REAL_RING;
     MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
   [NLIN_TAC [];
    MATCH_MP_TAC(REAL_ARITH `&0 <= q - p ==> p <= q`) THEN
    MATCH_MP_TAC CWPM_NONNEG_OF_MUL THEN EXISTS_TAC `cA * cR` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ONCE_REWRITE_TAC[REAL_MUL_SYM]] THEN
    ASM_REWRITE_TAC[];
    NLIN_TAC []; NLIN_TAC []; NLIN_TAC []]; ALL_TAC] THEN
  SUBGOAL_THEN `w pow 2 = &1 + q pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `cR * cR + sR * sR = &1` THEN UNDISCH_TAC `q * cR = sR` THEN
   UNDISCH_TAC `w * cR = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `p:real`; `q:real`; `w:real`]
    CWL_WALL_AXIS_MARGIN) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CWPA_COSINE_BOUND THEN EXISTS_TAC `sA:real` THEN
    ASM_REWRITE_TAC[REAL_POW_2];
    ASM_REAL_ARITH_TAC]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < w + (cA - sA) + q * (cA + sA)` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= q * (cA + sA)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cA * cR + sA * sR) * (&2 * cA + &2 * sA) <= (cA * cR + sA * sR) * uA /\
    (cA * sR - sA * cR) * (--(&47 / &20) * sA + (&33 / &20) * cA) <=
      (cA * sR - sA * cR) * vA /\
    sR * vR <= sR * (--sR * &1543 / &500 + cR * &2) /\
    &0 < (cR * cR) * (cwl_margin cA sA q w +
                      (aA - &1) * (w + (cA - sA) + q * (cA + sA)))`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LET_ADD THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cA * cR + sA * sR) * (&2 * cA + &2 * sA) +
    (cA * sR - sA * cR) * (--(&47 / &20) * sA + (&33 / &20) * cA) =
    cR * cwl_x cA sA + sR * cwl_y cA sA` ASSUME_TAC THENL
  [REWRITE_TAC[cwl_x; cwl_y] THEN UNDISCH_TAC `cA * cA + sA * sA = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cR * cR) * (cwl_margin cA sA q w +
                 (aA - &1) * (w + (cA - sA) + q * (cA + sA))) =
    cR * (cR * cwl_x cA sA + sR * cwl_y cA sA +
          aA * ((cA * cR + sA * sR) + (cA * sR - sA * cR))) +
    aA * cR + (&1543 / &500) * sR pow 2 - &2 * cR * sR - &4` ASSUME_TAC THENL
  [REWRITE_TAC[cwl_margin; cwl_x; cwl_y] THEN
   UNDISCH_TAC `cR * cR + sR * sR = &1` THEN UNDISCH_TAC `q * cR = sR` THEN
   UNDISCH_TAC `w * cR = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `cR * (cR * cwl_x cA sA + sR * cwl_y cA sA +
          aA * ((cA * cR + sA * sR) + (cA * sR - sA * cR))) <= cR * uR`
  ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC);;
