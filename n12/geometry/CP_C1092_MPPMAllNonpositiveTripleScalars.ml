(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositiveTripleScalars.lean      *)
(* (N12Compact.C1092MPPMAllNonpositive.TripleScalars), ALL-NEGATIVE-MIXED-   *)
(* FORWARD-ENDING section 3.  Normal is c977cc_normal; sector bounds         *)
(* (sine_order, cosine_order, dot_le_one, linear_arc_max) are C977CSB_*.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveCore.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092ANTS_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092ANTS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; C1092ANTS_LP_TAC]; ALL_TAC];;

let C1092ANTS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns);;

let C1092ANTS_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: G, k, delta (definitions) *)
let c1092ants_G = new_definition
 `c1092ants_G (d:real) (t:real) = (&1 - d) * (&1 - t) / d`;;
let c1092ants_k = new_definition
 `c1092ants_k (c:real) (s:real) (d:real) (t:real) = c * d + s * t`;;
let c1092ants_delta = new_definition
 `c1092ants_delta (c:real) (s:real) (d:real) (t:real) = c * t - s * d`;;

(* Lean: circle (private) *)
let C1092ANTS_CIRCLE = prove
 (`forall c s. c977cc_normal c s /\ &0 < s ==> &0 < c /\ c < &1 /\ &1 < c + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ANTS_NORMAL_TAC THEN
  C1092ANTS_PROD `&0 < s * s` THEN C1092ANTS_PROD `&0 < c * s` THEN
  REPEAT CONJ_TAC THENL
  [C1092ANTS_LP_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092ANTS_PROD `&0 <= (c - &1) * (c + &1)` THEN C1092ANTS_LP_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092ANTS_PROD `&0 <= (&1 - c - s) * (&1 + c + s)` THEN C1092ANTS_LP_TAC]);;

(* Lean: relative (private) *)
let C1092ANTS_RELATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 < c1092ants_k c s d t /\ c1092ants_k c s d t <= &1 /\
         c1092ants_k c s d t pow 2 + c1092ants_delta c s d t pow 2 = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[c1092ants_k; c1092ants_delta] THEN DISCH_TAC THEN C1092ANTS_NORMAL_TAC THEN
  C1092ANTS_PROD `&0 < c * d` THEN C1092ANTS_PROD `&0 <= s * t` THEN
  REPEAT CONJ_TAC THENL
  [C1092ANTS_LP_TAC; ASM_REWRITE_TAC[];
   UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `d * d + t * t = &1` THEN
   CONV_TAC REAL_RING]);;

(* the defining relation of G *)
let C1092ANTS_G_MUL = prove
 (`forall c s. c977cc_normal c s ==> c * c1092ants_G c s = (&1 - c) * (&1 - s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092ANTS_NORMAL_TAC THEN
  REWRITE_TAC[c1092ants_G] THEN
  SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [C1092ANTS_LP_TAC ORELSE RASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* Lean: G_spec (private) *)
let C1092ANTS_G_SPEC = prove
 (`forall c s. c977cc_normal c s ==> (&1 + s) * (c1092ants_G c s + &1 - s) = c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092ANTS_NORMAL_TAC THEN
  REWRITE_TAC[c1092ants_G] THEN
  SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_FIELD);;

(* Lean: endpoint *)
let C1092ANTS_ENDPOINT = prove
 (`forall c s. c977cc_normal c s /\ &0 < s ==> &0 < &1 - c - c1092ants_G c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ANTS_CIRCLE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ANTS_G_MUL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C1092ANTS_PROD `&0 < (&1 - c) * (c + s - &1)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092ANTS_PROD `&0 <= c * --(&1 - c - c1092ants_G c s)` THEN
  C1092ANTS_LP_TAC);;

(* Lean: G_difference *)
let C1092ANTS_G_DIFFERENCE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t
     ==> c1092ants_G d t - c1092ants_G c s <= (t - s) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ANTS_G_SPEC) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092ANTS_G_SPEC) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`c1092ants_G c s`,`gc:real`) THEN SPEC_TAC(`c1092ants_G d t`,`gd:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN C1092ANTS_NORMAL_TAC THEN
  ABBREV_TAC `II = (&1 - c) * (&1 - d) + (t - s) + s * (&2 - c - d + t)` THEN
  C1092ANTS_PROD `&0 <= (&1 - c) * (&1 - d)` THEN
  C1092ANTS_PROD `&0 <= s * (&2 - c - d + t)` THEN
  SUBGOAL_THEN `&0 <= II` ASSUME_TAC THENL [EXPAND_TAC "II" THEN C1092ANTS_LP_TAC; ALL_TAC] THEN
  C1092ANTS_PROD `&0 <= (t - s) * II` THEN
  SUBGOAL_THEN `(c + d) * (&1 + s) * ((&1 + t) * (gd - gc) - t * (t - s)) = --(t - s) * II`
  ASSUME_TAC THENL
  [EXPAND_TAC "II" THEN
   UNDISCH_TAC `(&1 + s) * (gc + &1 - s) = c` THEN UNDISCH_TAC `(&1 + t) * (gd + &1 - t) = d` THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `d * d + t * t = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`(c + d) * (&1 + s)`; `t * (t - s) - (&1 + t) * (gd - gc)`] C1092ANTS_CANCEL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN C1092ANTS_LP_TAC; C1092ANTS_LP_TAC];
   DISCH_TAC] THEN
  C1092ANTS_PROD `&0 <= (t - s) * (&1 - t)` THEN
  MP_TAC(SPECL [`&1 + t`; `(t - s) / &2 - (gd - gc)`] C1092ANTS_CANCEL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092ANTS_LP_TAC; REAL_ARITH_TAC]);;

(* Lean: delta_difference (private) *)
let C1092ANTS_DELTA_DIFFERENCE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t
     ==> t - s <= c1092ants_delta c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ANTS_NORMAL_TAC THEN
  REWRITE_TAC[c1092ants_delta] THEN
  C1092ANTS_PROD `&0 <= (&1 - c) * (&1 - d)` THEN C1092ANTS_PROD `&0 <= s * t` THEN
  C1092ANTS_PROD `&0 <= (t - s) * ((&1 - c) * (&1 - d) + s * t)` THEN
  SUBGOAL_THEN `(c + d) * ((c * t - s * d) - (t - s)) = (t - s) * ((&1 - c) * (&1 - d) + s * t)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `d * d + t * t = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`c + d:real`; `(c * t - s * d) - (t - s)`] C1092ANTS_CANCEL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092ANTS_LP_TAC; REAL_ARITH_TAC]);;

(* Lean: source_before *)
let C1092ANTS_SOURCE_BEFORE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 < s /\ &0 < t /\
             c1092ants_delta c s d t <= &0
             ==> &0 < d * (&1 - c) + (&1 - d) * (s - c1092ants_k c s d t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ANTS_CIRCLE) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092ANTS_CIRCLE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092ANTS_RELATIVE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C977CSB_SINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `c1092ants_delta c s d t <= &0` THEN
                  REWRITE_TAC[c1092ants_delta] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092ANTS_PROD `&0 <= d * (d - c)` THEN
  C1092ANTS_PROD `&0 <= (&1 - d) * (&1 - c1092ants_k c s d t)` THEN
  C1092ANTS_PROD `&0 < (&1 - d) * (d + s - &1)` THEN
  C1092ANTS_LP_TAC);;

(* Lean: source_after *)
let C1092ANTS_SOURCE_AFTER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 < s /\ &0 < t /\
             &0 <= c1092ants_delta c s d t
             ==> &0 < d * (&1 - c) + (&1 - d) * (s - c1092ants_k c s d t) +
                      d * c1092ants_delta c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092ANTS_CIRCLE) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_SINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 <= c1092ants_delta c s d t` THEN
                  REWRITE_TAC[c1092ants_delta] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  STRIP_TAC THEN C1092ANTS_NORMAL_TAC THEN
  REWRITE_TAC[c1092ants_k; c1092ants_delta] THEN
  SUBGOAL_THEN `d * (d * d + t * t) = d` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`;
                `d * (&2 - d - t)`; `d * d - (&1 - d) * (&1 - t)`] C977CSB_LINEAR_ARC_MAX) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN C1092ANTS_LP_TAC;
    C1092ANTS_PROD `&0 <= d * (d - t)` THEN C1092ANTS_LP_TAC];
   DISCH_TAC] THEN
  C1092ANTS_PROD `&0 < (&1 - d) * (d + t - &1)` THEN
  C1092ANTS_LP_TAC);;

(* Lean: target_after *)
let C1092ANTS_TARGET_AFTER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 < s /\ &873 / &1000 < c /\
             &0 <= c1092ants_delta c s d t
             ==> &0 < c1092ants_k c s d t * (&1 - c) +
                      c1092ants_delta c s d t * (&1 - (&7 / &20) * (c - s)) - c1092ants_G d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_SINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 <= c1092ants_delta c s d t` THEN
                  REWRITE_TAC[c1092ants_delta] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092ANTS_RELATIVE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ANTS_ENDPOINT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092ANTS_G_DIFFERENCE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092ANTS_DELTA_DIFFERENCE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092ANTS_NORMAL_TAC THEN
  ABBREV_TAC `k = c1092ants_k c s d t` THEN ABBREV_TAC `z = c1092ants_delta c s d t` THEN
  SUBGOAL_THEN `&1 - k <= z` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092ANTS_PROD `&0 < (&1 - k - z) * (&1 - k + z)` THEN
   C1092ANTS_PROD `&0 <= k * (&1 - k)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092ANTS_LP_TAC; ALL_TAC] THEN
  C1092ANTS_PROD `&0 <= (z - (&1 - k)) * (&1 - c)` THEN
  C1092ANTS_PROD `&0 <= z * (&127 / &1000 - (&1 - c))` THEN
  C1092ANTS_PROD `&0 <= z * (&1 - (&7 / &20) * (c - s) - &13 / &20)` THEN
  C1092ANTS_LP_TAC);;

(* Lean: target_before *)
let C1092ANTS_TARGET_BEFORE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 < s /\ &0 < t /\
             &873 / &1000 < c /\ &873 / &1000 < d /\ c1092ants_delta c s d t <= &0
             ==> &0 < c1092ants_k c s d t * (&1 - c) +
                      (&13 / &50) * c1092ants_delta c s d t * s - c1092ants_G d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092ANTS_RELATIVE) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092ANTS_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092ANTS_NORMAL_TAC THEN
  SUBGOAL_THEN `c1092ants_k c s d t * (&1 - c) + (&13 / &50) * c1092ants_delta c s d t * s -
                (&1 - d) =
                c1092ants_k c s d t - &1 + (&37 / &50) * s * --c1092ants_delta c s d t`
  ASSUME_TAC THENL
  [REWRITE_TAC[c1092ants_k; c1092ants_delta] THEN UNDISCH_TAC `c * c + s * s = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `--c1092ants_delta c s d t <= s /\ &1 / &2 <= c1092ants_k c s d t`
  STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092ants_k; c1092ants_delta] THEN
   C1092ANTS_PROD `&0 <= s * (&1 - d)` THEN C1092ANTS_PROD `&0 <= c * t` THEN
   C1092ANTS_PROD `&0 <= (c - &873 / &1000) * (d - &873 / &1000)` THEN
   C1092ANTS_PROD `&0 <= s * t` THEN C1092ANTS_LP_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = c1092ants_k c s d t` THEN ABBREV_TAC `z = c1092ants_delta c s d t` THEN
  C1092ANTS_PROD `&0 <= s * ((&37 / &50) * (&1 + k) - &1)` THEN
  C1092ANTS_PROD `&0 <= --z * ((&37 / &50) * s * (&1 + k) - --z)` THEN
  SUBGOAL_THEN `(&1 + k) * (k - &1 + (&37 / &50) * s * --z) =
                --z * ((&37 / &50) * s * (&1 + k) - --z)` ASSUME_TAC THENL
  [UNDISCH_TAC `k pow 2 + z pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 + k`; `k - &1 + (&37 / &50) * s * --z`] C1092ANTS_CANCEL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092ANTS_LP_TAC; DISCH_TAC] THEN
  C1092ANTS_LP_TAC);;
