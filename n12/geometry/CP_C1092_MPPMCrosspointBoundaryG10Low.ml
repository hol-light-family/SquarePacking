(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryG10Low.lean         *)
(* (N12Compact.C1092MPPMCrosspointSupport), BOUNDARY-SCALARS section 8.1.   *)
(* Normal is c977cc_normal; G10, FC, kE, deltaE, E0, Quarter are c1092mcs_*; *)
(* FC_low_cap C1092G10_FC_LOW_CAP; lower_endpoint_D                         *)
(* C1092MCBE_LOWER_ENDPOINT_D; sector bounds C977CSB_*; UnitCircleChord      *)
(* CCUCC_*; norm_le C1092NPP_NORM_LE.                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG10Clamp.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryEndpoints.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessorScalars.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

let C1092G10L_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092G10L_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092G10L_LP_TAC; ALL_TAC];;

let C1092G10L_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: G10_upper_formula *)
let C1092G10L_G10_UPPER_FORMULA = prove
 (`forall c s d t h r. c1092mcs_quarter h r /\ &0 <= c1092mcs_deltaE d t h r
     ==> c1092mcs_G10 c s d t h r =
         (&1 + h * r - &2 * h - r - c1092mcs_FC c s h r) * d +
         (r pow 2 - (&36 / &25) * r) * t + r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mcs_quarter] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[c1092mcs_G10; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REWRITE_TAC[c1092mcs_kE; c1092mcs_deltaE; c1092mcs_E0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: G10_lower_formula *)
let C1092G10L_G10_LOWER_FORMULA = prove
 (`forall c s d t h r. c1092mcs_quarter h r /\ c1092mcs_deltaE d t h r <= &0
     ==> c1092mcs_G10 c s d t h r =
         (h * (h + r) - &2 * h - r - c1092mcs_FC c s h r) * d +
         (r * (h + r - &36 / &25)) * t + r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mcs_quarter] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[c1092mcs_G10; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REWRITE_TAC[c1092mcs_kE; c1092mcs_deltaE; c1092mcs_E0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: low_quarter_bounds *)
let C1092G10L_LOW_QUARTER_BOUNDS = prove
 (`forall h r. c1092mcs_quarter h r /\ &4 / &5 <= h /\ r <= &3 / &5
         ==> c977cc_normal h r /\ h <= &1 /\ &1 <= h + r /\ h + r <= &7 / &5`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mcs_quarter] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal h r` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `h:real`; `r:real`] C977CSB_DOT_LE_ONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
                  DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN C1092G10L_NORMAL_TAC THEN C1092G10L_LP_TAC);;

(* Lean: before (private) *)
let C1092G10L_BEFORE = prove
 (`forall d t h r P Q. c977cc_normal d t /\ c977cc_normal h r /\ t <= r /\ Q <= &0 /\
                 &0 <= P * r - Q * h
                 ==> P * h + Q * r <= P * d + Q * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= P` THENL
  [MP_TAC(SPECL [`h:real`; `r:real`; `d:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   C1092G10L_PROD `&0 <= P * (d - h)` THEN C1092G10L_PROD `&0 <= --Q * (r - t)` THEN
   C1092G10L_LP_TAC;
   C1092G10L_NORMAL_TAC THEN
   MP_TAC(SPECL [`h:real`; `r:real`; `d:real`; `t:real`; `--P`; `--Q`] CCUCC_INCREASING) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092G10L_LP_TAC; C1092G10L_LP_TAC ORELSE REAL_ARITH_TAC]]);;

(* Lean: after (private) *)
let C1092G10L_AFTER = prove
 (`forall d t h r P Q. c977cc_normal d t /\ c977cc_normal h r /\ r <= t /\ P <= &0 /\ Q <= &0 /\
                 &0 <= Q * h - P * r
                 ==> P * h + Q * r <= P * d + Q * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092G10L_NORMAL_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `d:real`; `t:real`; `--P`; `--Q`] CCUCC_DECREASING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092G10L_LP_TAC; REAL_ARITH_TAC]);;

(* Lean: G10_low_nonnegative *)
let C1092G10L_G10_LOW_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c1092mcs_quarter h r /\ &4 / &5 <= h /\ r <= &3 / &5
                 ==> &0 <= c1092mcs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092G10L_LOW_QUARTER_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092G10_FC_LOW_CAP) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MCBE_LOWER_ENDPOINT_D) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092G10L_NORMAL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter; REAL_POW_2] o
    check (fun th -> can (term_match [] `c1092mcs_quarter x y`) (concl th))) THEN
  C1092G10L_PROD `&0 <= ((--(&3496 / &3125) * h + (&11387 / &12500) * r) -
                          c1092mcs_FC c s h r) * d` THEN
  SUBGOAL_THEN `r * (h * h + r * r) = r /\ h * (h * h + r * r) = h` STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c1092mcs_deltaE d t h r` THENL
  [MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
     C1092G10L_G10_UPPER_FORMULA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   C1092G10L_PROD `&0 <= r * (&36 / &25 - r)` THEN
   SUBGOAL_THEN `&0 <= (&1 + h * r - &2 * h - r - (--(&3496 / &3125) * h + (&11387 / &12500) * r)) - h * (r - &36 / &25)` ASSUME_TAC THENL
   [C1092G10L_LP_TAC; ALL_TAC] THEN
   C1092G10L_PROD `&0 <= r * ((&1 + h * r - &2 * h - r - (--(&3496 / &3125) * h + (&11387 / &12500) * r)) - h * (r - &36 / &25))` THEN
   MP_TAC(SPECL [`h:real`; `r:real`; `d:real`; `t:real`] C977CSB_SINE_ORDER) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= c1092mcs_deltaE d t h r` THEN
    REWRITE_TAC[c1092mcs_deltaE] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
   MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`;
                 `&1 + h * r - &2 * h - r - (--(&3496 / &3125) * h + (&11387 / &12500) * r)`; `r pow 2 - (&36 / &25) * r`] C1092G10L_BEFORE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN C1092G10L_LP_TAC; DISCH_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
   REWRITE_TAC[REAL_POW_2] THEN C1092G10L_LP_TAC;
   SUBGOAL_THEN `c1092mcs_deltaE d t h r <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
     C1092G10L_G10_LOWER_FORMULA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   C1092G10L_PROD `&0 <= r * --(h + r - &36 / &25)` THEN
   C1092G10L_PROD `&0 <= r * (h + r - &1)` THEN
   C1092G10L_PROD `&0 <= r * t` THEN
   ASM_CASES_TAC `&0 <= h * (h + r) - &2 * h - r - (--(&3496 / &3125) * h + (&11387 / &12500) * r)` THENL
   [C1092G10L_PROD `&0 <= (h * (h + r) - &2 * h - r - (--(&3496 / &3125) * h + (&11387 / &12500) * r)) * d` THEN
    C1092G10L_PROD `&0 <= r * (&1 - t)` THEN
    C1092G10L_PROD `&0 <= (r * (h + r - &36 / &25) - --(&11 / &25) * r) * t` THEN
    C1092G10L_LP_TAC;
    ASM_CASES_TAC `&0 <= --(&1746 / &3125) * h + (&23887 / &12500) * r` THENL
    [C1092G10L_PROD `&0 <= r * (--(&1746 / &3125) * h + (&23887 / &12500) * r)` THEN
     MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C977CSB_SINE_ORDER) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c1092mcs_deltaE d t h r <= &0` THEN
      REWRITE_TAC[c1092mcs_deltaE] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
     MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`;
                   `h * (h + r) - &2 * h - r - (--(&3496 / &3125) * h + (&11387 / &12500) * r)`; `r * (h + r - &36 / &25)`] C1092G10L_AFTER) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092G10L_LP_TAC; DISCH_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
     REWRITE_TAC[REAL_POW_2] THEN C1092G10L_LP_TAC;
     SUBGOAL_THEN `r < (&293 / &1000) * h` ASSUME_TAC THENL [C1092G10L_LP_TAC; ALL_TAC] THEN
     C1092G10L_PROD `&0 < ((&293 / &1000) * h - r) * ((&293 / &1000) * h + r)` THEN
     SUBGOAL_THEN `&959 / &1000 < h` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092G10L_PROD `&0 <= (&959 / &1000 - h) * (&959 / &1000 + h)` THEN
      C1092G10L_LP_TAC; ALL_TAC] THEN
     C1092G10L_PROD `&0 <= h * (h - &959 / &1000)` THEN
     C1092G10L_PROD `&0 <= r * (h - &959 / &1000)` THEN
     SUBGOAL_THEN `--(&7 / &10) * r <= h * (h + r) - &2 * h - r - (--(&3496 / &3125) * h + (&11387 / &12500) * r)` ASSUME_TAC THENL
     [C1092G10L_LP_TAC; ALL_TAC] THEN
     C1092G10L_PROD `&0 <= ((h * (h + r) - &2 * h - r - (--(&3496 / &3125) * h + (&11387 / &12500) * r)) - --(&7 / &10) * r) * d` THEN
     C1092G10L_PROD `&0 <= (r * (h + r - &36 / &25) - --(&11 / &25) * r) * t` THEN
     MP_TAC(SPECL [`&7 / &10`; `&11 / &25`; `d:real`; `t:real`; `&1`] C1092NPP_NORM_LE) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
     C1092G10L_PROD `&0 <= r * (&1 - (&7 / &10) * d - (&11 / &25) * t)` THEN
     C1092G10L_LP_TAC]]]);;
