(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveSuccessorScalars.lean  *)
(* (N12Compact.C1092MPPMInwardPositive.SuccessorScalars).  Whole-arc margins *)
(* for POSITIVE-MISSING-INWARD-SUCCESSOR.  Normal: c977cc_normal;            *)
(* normal_bounds: C977CC_NORMAL_BOUNDS; normal_sum: C1092MANS_NORMAL_SUM;    *)
(* sine_order: C977CSB_SINE_ORDER; UnitCircleChord.linear_nonnegative:       *)
(* CCUCC_LINEAR_NONNEGATIVE.  Tag C1092IPSS_.                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveProfile.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* Lean: k *)
let c1092ipss_k = new_definition
 `c1092ipss_k (c:real) (s:real) (d:real) (t:real) = c * d + s * t`;;

(* Lean: delta *)
let c1092ipss_delta = new_definition
 `c1092ipss_delta (c:real) (s:real) (d:real) (t:real) = c * t - s * d`;;

(* Lean: A *)
let c1092ipss_A = new_definition
 `c1092ipss_A (c:real) (s:real) =
    &27 / &20 - c + s - (&3 / &4) * s pow 2 - (&13 / &20) * c * s`;;

(* Lean: B *)
let c1092ipss_B = new_definition
 `c1092ipss_B (c:real) (s:real) =
    &2 - c - s - (&13 / &20) * s pow 2 + (&3 / &4) * c * s`;;

let C1092IPSS_LIN = NLIN_TAC ~deg2:false [];;

let C1092IPSS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092IPSS_LIN; ALL_TAC];;

let C1092IPSS_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092IPSS_LIN; ALL_TAC];;

let C1092IPSS_SUMS_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C1092MANS_NORMAL_SUM th)) ns);;

(* Lean: relative *)
let C1092IPSS_RELATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 < c1092ipss_k c s d t /\ c1092ipss_k c s d t <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MANS_NORMALS_TAC THEN
  REWRITE_TAC[c1092ipss_k] THEN
  C1092IPSS_PROD `&0 < c * d` THEN C1092IPSS_PROD `&0 <= s * t` THEN
  CONJ_TAC THENL
   [C1092IPSS_LIN;
    NLIN_TAC [SQ_NONNEG `c - d:real`; SQ_NONNEG `s - t:real`]]);;

(* Lean: source_margin *)
let C1092IPSS_SOURCE_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 < t
     ==> &0 < &1 - c - (&2 / &5) * s + c1092ipss_k c s d t * (&1 - d + (&2 / &5) * t) -
              (&7 / &20) * c1092ipss_delta c s d t * (d + t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MANS_NORMALS_TAC THEN
  ABBREV_TAC `P = &2 - d - (&13 / &20) * t * t - (&1 / &20) * d * t` THEN
  ABBREV_TAC `Q = t - (&13 / &20) * d * t - (&1 / &20) * d * d` THEN
  C1092IPSS_PROD `&0 <= (d - t) * (d + t)` THEN
  C1092IPSS_FACT `t * t <= &1 / &2` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `d - t:real`] [`d * t <= &1 / &2`] THEN
  C1092IPSS_PROD `&0 <= (&1 - d) * ((&13 / &20) * (&1 + d) - &1)` THEN
  C1092IPSS_PROD `&0 < d * t` THEN
  C1092IPSS_FACT `&0 < P` THEN C1092IPSS_FACT `P < &1` THEN
  C1092IPSS_PROD `&0 <= t * (&1 - d)` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`] [`&0 <= Q`] THEN
  C1092IPSS_PROD `&0 <= P * (&1 - c)` THEN C1092IPSS_PROD `&0 <= s * Q` THEN
  SUBGOAL_THEN `&1 - c - (&2 / &5) * s + c1092ipss_k c s d t * (&1 - d + (&2 / &5) * t) -
                (&7 / &20) * c1092ipss_delta c s d t * (d + t) = &1 - P * c + Q * s`
    SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN REWRITE_TAC[c1092ipss_k; c1092ipss_delta] THEN
    UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092IPSS_LIN);;

(* Lean: downward_margin *)
let C1092IPSS_DOWNWARD_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 < &1 - (&7 / &20) * (c + s) - (&7 / &20) * c1092ipss_k c s d t * (d + t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092IPSS_SUMS_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092IPSS_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092IPSS_PROD `&0 <= (&1 - c1092ipss_k c s d t) * (d + t)` THEN
  C1092IPSS_LIN);;

(* Lean: coefficient_bounds *)
let C1092IPSS_COEFFICIENT_BOUNDS = prove
 (`forall c s. c977cc_normal c s
     ==> c1092ipss_A c s <= &13 / &20 /\ c1092ipss_A c s + c1092ipss_B c s <= &7 / &5`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092IPSS_SUMS_TAC THEN C1092MANS_NORMALS_TAC THEN
  C1092IPSS_PROD `&0 <= (c - s) * (&1 - (&7 / &10) * (c + s))` THEN
  C1092IPSS_PROD `&0 <= s * (c - s)` THEN
  C1092IPSS_PROD `&0 <= (&1 - c) * ((&3 / &5) * (&1 + c) - &1)` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s:real`] [`c * s <= &1 / &2`] THEN
  REWRITE_TAC[c1092ipss_A; c1092ipss_B; REAL_POW_2] THEN
  CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`]);;

(* Lean: target_after *)
let C1092IPSS_TARGET_AFTER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 < &1 - d - t + c1092ipss_k c s d t * (&1 - (&7 / &20) * (c + s)) +
              c1092ipss_delta c s d t * (&1 - c - (&2 / &5) * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IPSS_COEFFICIENT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092IPSS_SUMS_TAC THEN C1092MANS_NORMALS_TAC THEN
  ABBREV_TAC `P = c1092ipss_A c s` THEN ABBREV_TAC `Q = c1092ipss_B c s` THEN
  SUBGOAL_THEN `&1 - d - t + c1092ipss_k c s d t * (&1 - (&7 / &20) * (c + s)) +
                c1092ipss_delta c s d t * (&1 - c - (&2 / &5) * s) = &1 - P * d - Q * t`
    SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN
    REWRITE_TAC[c1092ipss_k; c1092ipss_delta; c1092ipss_A; c1092ipss_B] THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `P <= Q` THENL
   [C1092IPSS_PROD `&0 <= (d - t) * (Q - P)` THEN
    C1092IPSS_PROD `&0 <= (&7 / &5 - P - Q) * (d + t)` THEN C1092IPSS_LIN;
    C1092IPSS_PROD `&0 <= t * (P - Q)` THEN
    C1092IPSS_PROD `&0 <= (&13 / &20 - P) * (d + t)` THEN C1092IPSS_LIN]);;

(* Lean: ordered_relative_lower (private) *)
let C1092IPSS_ORDERED_RELATIVE_LOWER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ c1092ipss_delta c s d t <= &0
     ==> (&7 / &10) * (d + t) <= c1092ipss_k c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C977CSB_SINE_ORDER) THEN
  ASM_REWRITE_TAC[GSYM c1092ipss_delta] THEN DISCH_TAC THEN
  C1092IPSS_SUMS_TAC THEN C1092MANS_NORMALS_TAC THEN
  ABBREV_TAC `w = sqrt(&2) / &2` THEN
  SUBGOAL_THEN `&0 <= w /\ w * w + w * w = &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN SIMP_TAC[SQRT_POS_LE; REAL_LE_DIV; REAL_POS] THEN
    REWRITE_TAC[REAL_ARITH `x / &2 * x / &2 + x / &2 * x / &2 = (x * x) / &2`] THEN
    SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_POS] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &10 <= w` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IPSS_PROD `&0 < (&7 / &10 - w) * (&7 / &10 + w)` THEN C1092IPSS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `s <= w` ASSUME_TAC THENL
   [C1092IPSS_PROD `&0 <= (c - s) * (c + s)` THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IPSS_PROD `&0 < (s - w) * (s + w)` THEN C1092IPSS_LIN; ALL_TAC] THEN
  C1092IPSS_PROD `&0 <= (w - &7 / &10) * (d + t)` THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `w:real`; `w:real`; `c:real`; `s:real`;
                `--(&7 / &10) * (d + t)`; `d:real`; `t:real`] CCUCC_LINEAR_NONNEGATIVE) THEN
  REWRITE_TAC[REAL_POW_2; c1092ipss_k] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092IPSS_LIN; DISCH_TAC THEN C1092IPSS_LIN]);;

(* Lean: target_before *)
let C1092IPSS_TARGET_BEFORE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ c1092ipss_delta c s d t <= &0
     ==> &0 < &1 - d - t + c1092ipss_k c s d t * (&1 - (&7 / &20) * (c + s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092IPSS_SUMS_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092IPSS_RELATIVE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092IPSS_ORDERED_RELATIVE_LOWER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C1092IPSS_PROD `&0 <= c1092ipss_k c s d t * (&1 - (&7 / &20) * (c + s) - &1 / &2)` THEN
  C1092IPSS_LIN);;
