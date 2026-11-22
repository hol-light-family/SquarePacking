(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/InwardSignScalars.lean              *)
(* (namespace N12Compact.Completion.OtherCases.InwardSignScalars).          *)
(* Continuous margins for the inward-sign theorem.  CanonicalScalars.bounds:*)
(* CCCS_BOUNDS; SharpPointScalars.half_upper / half_before: OCSPS_*;        *)
(* CanonicalProjection.before: CCCP_BEFORE.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let OCISS_BOUNDS_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC];;

(* Lean: affine_negative *)
let OCISS_AFFINE_NEGATIVE = prove
 (`forall d r A B. &0 < d /\ &0 <= r /\ r <= d /\ A < &0 /\ A + B < &0
             ==> d * A + r * B < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d * A + r * B = (d - r) * A + r * (A + B)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r:real = d` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < d * --(A + B) ==> d * (A + B) < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 < x * --A /\ &0 <= r * --B ==> x * A + r * B < &0`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: x_negative *)
let OCISS_X_NEGATIVE = prove
 (`forall c s. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> (&1 - c) * (c + s - &1) - &13 / &50 * s < &0`,
  REPEAT STRIP_TAC THEN OCISS_BOUNDS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&0 <= s * (&1 + c - &2 * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 + c) * (s - &2 * (&1 - c))` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= s * (&1 + c - &2 * s)` THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s - &2 * (&1 - c)` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 C1092WPS_CANCEL) THEN EXISTS_TAC `&1 + c` THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - c) * (&3 / &7 - (c + s - &1))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= s - &2 * (&1 - c)` THEN UNDISCH_TAC `&0 < s` THEN
  REAL_ARITH_TAC);;

(* Lean: c_strict (private) *)
let OCISS_C_STRICT = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 ==> c < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_TAC [SQ_NONNEG `c - &1`]);;

(* Lean: negative_bar *)
let OCISS_NEGATIVE_BAR = prove
 (`forall c s d r. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
             &0 < d /\ &0 <= r /\ r <= d
             ==> d * ((c - &1) * (c + s) + &13 / &50 * s * (s - c)) +
                 r * ((c - &1) * (c - s) + &13 / &50 * s * (c + s)) < &0`,
  REPEAT STRIP_TAC THEN OCISS_BOUNDS_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCISS_C_STRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC OCISS_AFFINE_NEGATIVE THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (&1 - c) * (c + s) /\ &0 <= s * (c - s) /\
                &0 < (&1 - c) * (&37 / &25 * c - &13 / &25)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
  REAL_ARITH_TAC);;

(* Lean: positive_bar *)
let OCISS_POSITIVE_BAR = prove
 (`forall c s d r. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
             &0 < d /\ &0 <= r /\ r <= d
             ==> d * ((c - &1) * (c - s) + &13 / &50 * s * (c + s) - &7 / &20) +
                 r * ((c - &1) * (c + s) + &13 / &50 * s * (s - c) + &7 / &20) < &0`,
  REPEAT STRIP_TAC THEN OCISS_BOUNDS_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCISS_C_STRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC OCISS_AFFINE_NEGATIVE THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= (&1 - c) * (c - s) /\ &0 <= c * (c - s) /\
                &0 < (&1 - c) * (&37 / &25 * c - &13 / &25)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
  REAL_ARITH_TAC);;

(* Lean: positive_floor *)
let OCISS_POSITIVE_FLOOR = prove
 (`forall c s d r. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
             &0 < d /\ &0 <= r /\ r <= d
             ==> d * (c * (&13 / &20 - c)) +
                 r * ((&1 - c) * (s - &1) - &13 / &50 * s + &7 / &20 * c) < &0`,
  REPEAT STRIP_TAC THEN OCISS_BOUNDS_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCISS_X_NEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC OCISS_AFFINE_NEGATIVE THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < c * (c - &13 / &20)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(&1 - c) * (c + s - &1) - &13 / &50 * s < &0` THEN
  REAL_ARITH_TAC);;

(* Lean: difference_order *)
let OCISS_DIFFERENCE_ORDER = prove
 (`forall c s d r. &0 < c /\ &0 <= s /\ &0 < d /\ &0 <= r /\
             c pow 2 + s pow 2 = &1 /\ d pow 2 + r pow 2 = &1 /\
             c * r - s * d <= &0
             ==> c - s <= d - r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (s * d - c * r) * (s * d + c * r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(c * c) * (r * r) - (s * s) * (d * d) = r * r - s * s` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `d * d + r * r = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `r <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (r - s) * (r + s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 <= (s * d - c * r) * (s * d + c * r)` THEN
    UNDISCH_TAC `(c * c) * (r * r) - (s * s) * (d * d) = r * r - s * s` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c <= d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (s - r) * (s + r) /\ &0 < (c - d) * (c + d)` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `d * d + r * r = &1` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: projection_cap *)
let OCISS_PROJECTION_CAP = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
         ==> c + &13 / &50 * s < &517 / &500`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (c + &13 / &50 * s - &517 / &500) * (c + &13 / &50 * s + &517 / &500)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&13 / &50 * c - s` REAL_LE_SQUARE) THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC);;

(* Lean: short_arc *)
let OCISS_SHORT_ARC = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ &1 < c + &13 / &50 * s
         ==> &87 / &100 < c /\ s < &49 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &50`] OCSPS_HALF_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&2331 / &2669`; `&1300 / &2669`; `&13 / &50`]
    OCSPS_HALF_BEFORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&2331 / &2669`; `&1300 / &2669`; `&0`; `&1`]
    CCCP_BEFORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN DISCH_TAC THEN
  SUBGOAL_THEN `s < &49 / &100` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (&49 / &100 - s) * (&49 / &100 + s) /\
                &0 <= (&87 / &100 - c) * (&87 / &100 + c)` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
  REAL_ARITH_TAC);;
