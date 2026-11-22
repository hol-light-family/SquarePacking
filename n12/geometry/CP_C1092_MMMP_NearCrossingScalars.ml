(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NearCrossingScalars.lean            *)
(* (N12Compact.C1092MMMPNearCrossingScalars).  Small-angle half-angle        *)
(* crossing gaps.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_CenterCrosspointScalars.ml";;

let C1092NCS_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092NCS_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092NCS_LIN_TAC; DISCH_TAC];;

(* Lean: endpoint *)
let C1092NCS_ENDPOINT = prove
 (`forall c s z. c977cc_normal c s /\ &0 <= z /\ z <= &1 / &2 /\
           z * (&1 + c) = s /\ s * z = &1 - c
           ==> &0 <= &1 - c - z + c * s / &2 /\
               &0 <= &3 / &2 - z - &2 * c + c pow 2 / &2 + c * s / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092CCS_NORMAL_TAC THEN
  SUBGOAL_THEN `(&1 + z * z) * c = &1 - z * z /\ (&1 + z * z) * s = &2 * z`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + z * z) * (&1 + z * z) * (&1 - c - z + c * s / &2) =
                z * z * (&1 - z) * (&2 - z + z * z)` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z * z) * c = &1 - z * z` THEN
    UNDISCH_TAC `(&1 + z * z) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z * z` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  C1092NCS_LE_MUL_TAC `z * z` `&1 - z` THEN
  C1092NCS_LE_MUL_TAC `z * z * (&1 - z)` `&2 - z + z * z` THEN
  SUBGOAL_THEN `&0 <= &1 - c - z + c * s / &2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `&1 - c - z + c * s / &2`; `(&1 + z * z) * (&1 + z * z)`]
      REAL_LE_LMUL_EQ) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C1092NCS_LIN_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
      C1092NCS_LIN_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= (&1 - c) * (&1 - c)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN C1092NCS_LIN_TAC);;

(* Lean: first *)
let C1092NCS_FIRST = prove
 (`forall c s z h b. c977cc_normal c s /\ s <= &1 / &4 /\ &0 <= z /\ z <= &1 / &2 /\
               z * (&1 + c) = s /\ s * z = &1 - c /\
               &0 <= h /\ &0 <= b /\ h pow 2 + b pow 2 = &1 /\ &0 <= s * h - c * b
               ==> &0 <= &1 / &2 + h pow 2 / &2 + h * b / &2 + h * (c + z - &2) +
                         b * (s - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `z:real`] C1092NCS_ENDPOINT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092CCS_ORDER_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092CCS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `b:real`] [`h <= &1`] THEN
  C1092NCS_LE_MUL_TAC `z:real` `&1 - s` THEN
  SUBGOAL_THEN `&0 <= c + z - &1` ASSUME_TAC THENL [C1092NCS_LIN_TAC; ALL_TAC] THEN
  C1092NCS_LE_MUL_TAC `h - c` `c + z - &1` THEN
  C1092NCS_LE_MUL_TAC `s - b` `--((s - &1) + h / &2)` THEN
  C1092NCS_LE_MUL_TAC `s:real` `h - c` THEN
  SUBGOAL_THEN `&0 <= (&1 - h) * (&1 - h)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  SUBGOAL_THEN `c * (c + z - &1) + s * ((s - &1) + c / &2) = &1 - c - z + c * s / &2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `z * (&1 + c) = s` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092NCS_LIN_TAC);;

(* Lean: second *)
let C1092NCS_SECOND = prove
 (`forall c s z h b. c977cc_normal c s /\ s <= &1 / &4 /\ &0 <= z /\ z <= &1 / &2 /\
               z * (&1 + c) = s /\ s * z = &1 - c /\
               &0 <= h /\ &0 <= b /\ h pow 2 + b pow 2 = &1 /\ s * h - c * b <= &0
               ==> &0 <= &1 / &2 + h pow 2 / &2 + h * b / &2 +
                         h * ((&1 - z) * c + (&13 / &50) * s pow 2 - &2) +
                         b * ((&1 - z) * s - (&13 / &50) * s * c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `z:real`] C1092NCS_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092CCS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092NCS_LE_MUL_TAC `c:real` `b:real` THEN C1092NCS_LE_MUL_TAC `s:real` `h:real` THEN
  C1092NCS_LE_MUL_TAC `c * b - s * h` `c * b + s * h` THEN
  SUBGOAL_THEN `(c * b - s * h) * (c * b + s * h) = b * b - s * s` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `h * h + b * b = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `s <= b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (s - b) * (s + b)`] THEN C1092NCS_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `h <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NCS_LE_MUL_TAC `b - s` `b + s` THEN
    NLIN_FACTS_TAC [] [`&0 < (h - c) * (h + c)`] THEN C1092NCS_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092CCS_QUADRATIC_MONOTONE) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  C1092NCS_LE_MUL_TAC `z:real` `&1 - c` THEN
  SUBGOAL_THEN `s / &2 <= z` ASSUME_TAC THENL [C1092NCS_LIN_TAC; ALL_TAC] THEN
  C1092NCS_LE_MUL_TAC `z - s / &2` `c:real` THEN
  C1092NCS_LE_MUL_TAC `s:real` `c / &2 - (&13 / &50) * s` THEN
  C1092NCS_LE_MUL_TAC `s:real` `&1 - z - (&13 / &50) * c` THEN
  SUBGOAL_THEN `(&1 - z) * c + (&13 / &50) * s * s - &1 <= &0 /\
                &0 <= (&1 - z) * s - (&13 / &50) * s * c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092NCS_LIN_TAC; ALL_TAC] THEN
  C1092NCS_LE_MUL_TAC `c - h` `--((&1 - z) * c + (&13 / &50) * s * s - &1)` THEN
  C1092NCS_LE_MUL_TAC `b - s` `(&1 - z) * s - (&13 / &50) * s * c` THEN
  SUBGOAL_THEN
   `(&1 - c) * (&1 - c) / &2 + c * s / &2 + c * ((&1 - z) * c + (&13 / &50) * s * s - &1) +
    s * ((&1 - z) * s - (&13 / &50) * s * c) = &3 / &2 - z - &2 * c + c * c / &2 + c * s / &2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN C1092NCS_LIN_TAC);;
