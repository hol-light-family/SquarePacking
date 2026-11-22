(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/CenterCrosspointScalars.lean        *)
(* (N12Compact.C1092MMMPCenterCrosspointScalars).  The small central-angle   *)
(* part of the MMMP center-to-crosspoint argument.                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShortWallPenalty.ml";;

let C1092CCS_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092CCS_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092CCS_LIN_TAC; DISCH_TAC];;

let C1092CCS_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

(* Lean: small_bounds (private) *)
let C1092CCS_SMALL_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ s <= &1 / &4
         ==> &19 / &20 <= c /\ &1 - c <= (&13 / &25) * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092CCS_NORMAL_TAC THEN
  C1092CCS_LE_MUL_TAC `&1 / &4 - s` `&1 / &4 + s` THEN
  SUBGOAL_THEN `&19 / &20 <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (&19 / &20 - c) * (&19 / &20 + c)`] THEN C1092CCS_LIN_TAC;
    ALL_TAC] THEN
  C1092CCS_LE_MUL_TAC `&1 - c` `(&13 / &25) * (&1 + c) - &1` THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN C1092CCS_LIN_TAC);;

(* Lean: order_bounds (private) *)
let C1092CCS_ORDER_BOUNDS = prove
 (`forall c s h b. c977cc_normal c s /\ &0 <= h /\ &0 <= b /\ h pow 2 + b pow 2 = &1 /\
             &0 <= s * h - c * b
             ==> c <= h /\ b <= s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092CCS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092CCS_LE_MUL_TAC `s:real` `h:real` THEN C1092CCS_LE_MUL_TAC `c:real` `b:real` THEN
  C1092CCS_LE_MUL_TAC `s * h - c * b` `s * h + c * b` THEN
  SUBGOAL_THEN `(s * h - c * b) * (s * h + c * b) = s * s - b * b` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `h * h + b * b = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `b <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (b - s) * (b + s)`] THEN C1092CCS_LIN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092CCS_LE_MUL_TAC `s - b` `s + b` THEN
  NLIN_FACTS_TAC [] [`&0 < (c - h) * (c + h)`] THEN C1092CCS_LIN_TAC);;

(* Lean: first *)
let C1092CCS_FIRST = prove
 (`forall c s h b. c977cc_normal c s /\ s <= &1 / &4 /\ &0 <= h /\ &0 <= b /\
             h pow 2 + b pow 2 = &1 /\ &0 <= s * h - c * b
             ==> &0 <= &1 / &2 + h pow 2 / &2 + h * b / &2 +
                       h * (c + s - (&17 / &20) * c * s + (&7 / &20) * s pow 2 - &2) +
                       b * (s - c + (&7 / &20) * c pow 2 - (&7 / &20) * c * s - s pow 2 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092CCS_SMALL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092CCS_ORDER_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092CCS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `b:real`] [`h <= &1`] THEN
  C1092CCS_LE_MUL_TAC `s:real` `&3 / &20 - (&17 / &100) * s` THEN
  C1092CCS_LE_MUL_TAC `s:real` `&1 - c` THEN
  SUBGOAL_THEN `&0 <= (c + s - (&17 / &20) * c * s + (&7 / &20) * s * s - &1)` ASSUME_TAC THENL [C1092CCS_LIN_TAC; ALL_TAC] THEN
  C1092CCS_LE_MUL_TAC `s:real` `c - &19 / &20` THEN
  C1092CCS_LE_MUL_TAC `&1 / &4 - s` `&267 / &400 - (&33 / &100) * (&1 / &4 + s)` THEN
  SUBGOAL_THEN `((s - c + (&7 / &20) * c * c - (&7 / &20) * c * s - s * s / &2) + h / &2) <= &0` ASSUME_TAC THENL [C1092CCS_LIN_TAC; ALL_TAC] THEN
  C1092CCS_LE_MUL_TAC `h - c` `(c + s - (&17 / &20) * c * s + (&7 / &20) * s * s - &1)` THEN
  C1092CCS_LE_MUL_TAC `s - b` `--((s - c + (&7 / &20) * c * c - (&7 / &20) * c * s - s * s / &2) + h / &2)` THEN
  C1092CCS_LE_MUL_TAC `s:real` `h - c` THEN
  C1092CCS_LE_MUL_TAC `&1 - c` `&1 - s / &2` THEN
  SUBGOAL_THEN `c * (c + s - (&17 / &20) * c * s + (&7 / &20) * s * s - &1) + s * ((s - c + (&7 / &20) * c * c - (&7 / &20) * c * s - s * s / &2) + c / &2) = (&1 - c) * (&1 - s / &2)` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - h) * (&1 - h)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  C1092CCS_LIN_TAC);;

(* Lean: quadratic_monotone *)
let C1092CCS_QUADRATIC_MONOTONE = prove
 (`forall c s h b. c977cc_normal c s /\ s <= &1 / &4 /\ &0 <= h /\ &0 <= b /\
             h pow 2 + b pow 2 = &1 /\ h <= c /\ s <= b
             ==> (&1 - c) pow 2 + c * s <= (&1 - h) pow 2 + h * b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092CCS_SMALL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092CCS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `h:real`] [`b <= &1`] THEN
  SUBGOAL_THEN `&0 <= (b + s) * (&2 - c - h - s) + h * (c + h)` ASSUME_TAC THENL
   [ASM_CASES_TAC `h <= &1 / &2` THENL
     [C1092CCS_LE_MUL_TAC `b + s` `&2 - c - h - s` THEN
      C1092CCS_LE_MUL_TAC `h:real` `c + h` THEN C1092CCS_LIN_TAC;
      C1092CCS_LE_MUL_TAC `b + s` `&2 - c - h` THEN
      C1092CCS_LE_MUL_TAC `h - &1 / &2` `c + h` THEN
      C1092CCS_LE_MUL_TAC `&1 / &4 - s` `b + s` THEN C1092CCS_LIN_TAC];
    ALL_TAC] THEN
  C1092CCS_LE_MUL_TAC `c - h` `(b + s) * (&2 - c - h - s) + h * (c + h)` THEN
  SUBGOAL_THEN
   `(b + s) * (((&1 - h) * (&1 - h) + h * b) - ((&1 - c) * (&1 - c) + c * s)) =
    (c - h) * ((b + s) * (&2 - c - h - s) + h * (c + h))` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `h * h + b * b = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `b + s = &0` THENL
   [SUBGOAL_THEN `b = &0 /\ s = &0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN C1092CCS_LIN_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c = &1 /\ h = &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
      UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `h * h + b * b = &1` THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN NLIN_TAC [];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&0`; `((&1 - h) * (&1 - h) + h * b) - ((&1 - c) * (&1 - c) + c * s)`;
                `b + s`] REAL_LE_LMUL_EQ) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (b + s) * (((&1 - h) * (&1 - h) + h * b) - ((&1 - c) * (&1 - c) + c * s))`
    MP_TAC THENL [C1092CCS_LIN_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Lean: second *)
let C1092CCS_SECOND = prove
 (`forall c s h b. c977cc_normal c s /\ s <= &1 / &4 /\ &0 <= h /\ &0 <= b /\
             h pow 2 + b pow 2 = &1 /\ s * h - c * b <= &0
             ==> &0 <= &1 / &2 + h pow 2 / &2 + h * b / &2 +
                       h * (c - c * s / &2 - &2) + b * (s - s pow 2 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092CCS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092CCS_LE_MUL_TAC `c:real` `b:real` THEN C1092CCS_LE_MUL_TAC `s:real` `h:real` THEN
  C1092CCS_LE_MUL_TAC `c * b - s * h` `c * b + s * h` THEN
  SUBGOAL_THEN `(c * b - s * h) * (c * b + s * h) = b * b - s * s` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `h * h + b * b = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `s <= b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (s - b) * (s + b)`] THEN C1092CCS_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `h <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092CCS_LE_MUL_TAC `b - s` `b + s` THEN
    NLIN_FACTS_TAC [] [`&0 < (h - c) * (h + c)`] THEN C1092CCS_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092CCS_QUADRATIC_MONOTONE) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  C1092CCS_LE_MUL_TAC `c:real` `s:real` THEN
  C1092CCS_LE_MUL_TAC `s:real` `&1 - s / &2` THEN
  C1092CCS_LE_MUL_TAC `c - h` `--(c - c * s / &2 - &1)` THEN
  C1092CCS_LE_MUL_TAC `b - s` `s - s * s / &2` THEN
  C1092CCS_LE_MUL_TAC `&1 - c` `&3 - c - s` THEN
  SUBGOAL_THEN
   `(&1 - c) * (&1 - c) / &2 + c * s / &2 + c * (c - c * s / &2 - &1) +
    s * (s - s * s / &2) = (&1 - c) * (&3 - c - s) / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN C1092CCS_LIN_TAC);;
