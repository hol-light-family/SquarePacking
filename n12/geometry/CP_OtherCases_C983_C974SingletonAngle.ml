(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974SingletonAngle.lean        *)
(* (N12Compact.Completion.OtherCases.C983.C974MissingCorner).                *)
(* MISSING-CORNER-MIDPOINT 1.2-1.4: the two actual square axes exclude every *)
(* K slope >= 3/4, and the reduced C974LowerFace.Input.  Conventions of      *)
(* CP_OtherCases_C983_C974MissingCornerSupports.ml (Input K W = c974mc_input,*)
(* OpenSquare invariants explicit in C974MCS_INV); C974LowerFace.Input is    *)
(* oc983lf_input.  (Lean header: "Source translation, uncompiled".)          *)
(* Tag C974SA_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974WallSign.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974SingletonAngleScalars.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LowerFace.ml";;

let C974SA_KW = [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                 `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;
let C974SA_LIN = NLIN_TAC ~deg2:false [];;
let C974SA_FACT t tac = SUBGOAL_THEN t ASSUME_TAC THENL [tac; ALL_TAC];;
let C974SA_MUL_TAC =
  (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC THEN RASM_ARITH_TAC;;

(* Lean: singleton_slope *)
let C974SA_SINGLETON_SLOPE = prove
 (c974mcs_tm (Printf.sprintf "!%s %s. %s /\\ &0 < sK /\\ sK <= cK /\\ &0 < sW /\\ sW <= cW
     ==> &4 * sK < &3 * cK" C974MCS_K C974MCS_W C974MCS_INV),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C974SA_FACT `&0 < cK /\ &0 < cW` RASM_ARITH_TAC THEN
  MP_TAC(SPECL C974SA_KW C974MC_WALL_POSITIVE_SLOPE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL C974SA_KW C974MC_SINGLETON_POSITIVE_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C974SA_FACT `&0 <= cW * (&4 * sK - &3 * cK)` C974SA_MUL_TAC THEN
  C974SA_FACT `&0 < cK * (&2 * cW - &3 * sW)` C974SA_MUL_TAC THEN
  C974SA_FACT `&0 < cK * cW` C974SA_MUL_TAC THEN
  C974SA_FACT `&0 < sK * cW - cK * sW` C974SA_LIN THEN
  MP_TAC(SPECL C974SA_KW C974MCS_POSITIVE_SUPPORT_OBSTRUCTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `x = sK / (&1 + cK)` THEN
  C974SA_FACT `x * (&1 + cK) = sK`
   (EXPAND_TAC "x" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN RASM_ARITH_TAC) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `cW:real`; SQ_NONNEG `sW:real`]
   [`sK < &1`; `cW <= &1`] THEN
  C974SA_FACT `&0 <= (&4 * sK - &3 * cK) * (&4 * sK + &3 * cK)` C974SA_MUL_TAC THEN
  NLIN_FACTS_TAC [] [`&3 / &5 <= sK`; `cK <= &4 / &5`] THEN
  C974SA_FACT `&1 / &3 <= x` (NLIN_TAC []) THEN
  C974SA_FACT `&0 <= &1 - cW + (&1 - sK) * (cW * x - sW)`
   (ASM_CASES_TAC `&0 <= cW * x - sW` THENL
     [C974SA_FACT `&0 <= (&1 - sK) * (cW * x - sW)` C974SA_MUL_TAC THEN C974SA_LIN;
      C974SA_FACT `&0 <= (sK - &3 / &5) * --(cW * x - sW)` C974SA_MUL_TAC THEN
      C974SA_FACT `&0 <= cW * (x - &1 / &3)` C974SA_MUL_TAC THEN
      C974SA_FACT `&13 / &15 * cW + &2 / &5 * sW < &1`
        (NLIN_TAC [SQ_NONNEG `&2 / &5 * cW - &13 / &15 * sW`]) THEN
      C974SA_LIN]) THEN
  C974SA_FACT `&0 < cW * (&1 - cW / &2) + sW * (&1 - cW)`
   (C974SA_FACT `&0 < cW * (&1 - cW / &2)` C974SA_MUL_TAC THEN
    C974SA_FACT `&0 <= sW * (&1 - cW)` C974SA_MUL_TAC THEN C974SA_LIN) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] C974SAS_SINGLETON_ANGLE_G) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `x:real`] C974SGN_QUARTER_DEFECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  C974SA_FACT `&0 <= (sK - &3 * cK / &4) * (cW * (&1 - cW / &2) + sW * (&1 - cW))`
    C974SA_MUL_TAC THEN
  C974SA_FACT `&0 < cK * ((&7 / &4) * cW - (&11 / &8) * cW pow 2 - (&1 / &4) * cW * sW -
                          sW / &4 - &1 / &4)` C974SA_MUL_TAC THEN
  C974SA_FACT `&0 < (cK * cW + sK * sW) * (&1 - cW) + (sK * cW - cK * sW) * (&1 - cW / &2) -
                    x * (&1 - sK)` C974SA_LIN THEN
  REWRITE_TAC[REAL_NOT_LT] THEN STRIP_TAC THEN C974SA_LIN);;

(* Lean: reduced_input *)
let C974SA_REDUCED_INPUT = prove
 (c974mcs_tm (Printf.sprintf "!%s %s. %s /\\ &0 < sK /\\ sK <= cK /\\ &0 < sW /\\ sW <= cW
     ==> oc983lf_input %s %s" C974MCS_K C974MCS_W C974MCS_INV C974MCS_K C974MCS_W),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C974SA_KW C974SA_SINGLETON_SLOPE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C974SA_KW C974MC_WALL_POSITIVE_SLOPE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL C974SA_KW C974MC_WALL_POSITIVE_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL C974SA_KW C974MC_SINGLETON_POSITIVE_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL C974SA_KW C974MC_SINGLETON_WALL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C974MCS_OPEN_TAC THEN REWRITE_TAC[oc983lf_input] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;
