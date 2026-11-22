(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/UnitCircleChord.lean               *)
(* (N12Compact.CommonCases.UnitCircleChord).  Chord interpolation and        *)
(* linear-support monotonicity on the first-quadrant unit arc.  Scalar.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: cosine_order *)
let CCUCC_COSINE_ORDER = prove
 (`forall c s d t. &0 <= c /\ &0 <= d /\ c pow 2 + s pow 2 = &1 /\ d pow 2 + t pow 2 = &1 /\
             &0 <= s /\ &0 <= t /\ s <= t ==> d <= c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < (d - c) * (d + c)`; `&0 <= (t - s) * (t + s)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: cross_order *)
let CCUCC_CROSS_ORDER = prove
 (`forall c s d t. &0 <= c /\ &0 <= d /\ c pow 2 + s pow 2 = &1 /\ d pow 2 + t pow 2 = &1 /\
             &0 <= s /\ &0 <= t /\ s <= t ==> &0 <= c * t - s * d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CCUCC_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= c * (t - s)`; `&0 <= s * (c - d)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: linear_nonnegative *)
let CCUCC_LINEAR_NONNEGATIVE = prove
 (`forall c s d t h r b A B.
     &0 <= c /\ &0 <= d /\ &0 <= h /\
     c pow 2 + s pow 2 = &1 /\ d pow 2 + t pow 2 = &1 /\ h pow 2 + r pow 2 = &1 /\
     s <= r /\ r <= t /\ &0 <= A /\
     &0 <= b + A * c + B * s /\ &0 <= b + A * d + B * t
     ==> &0 <= b + A * h + B * r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = t` THENL
   [SUBGOAL_THEN `r:real = s` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h:real = c` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
       [NLIN_FACTS_TAC [] [`&0 < (h - c) * (h + c)`];
        NLIN_FACTS_TAC [] [`&0 < (c - h) * (c + h)`]] THEN
      NLIN_TAC ~deg2:false [];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t - s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(t - r) * c + (r - s) * d <= (t - s) * h` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= ((r - s) * (t - r)) * ((c - d) * (c - d) + (t - s) * (t - s))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_SQUARE]];
      ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (t - s) * h`;
      `&0 < ((t - r) * c + (r - s) * d - (t - s) * h) *
            ((t - r) * c + (r - s) * d + (t - s) * h)`] THEN
    SUBGOAL_THEN
     `(t - s) * (t - s) * (h * h) - ((t - r) * c + (r - s) * d) * ((t - r) * c + (r - s) * d) =
      (r - s) * (t - r) * ((c - d) * (c - d) + (t - s) * (t - s))` ASSUME_TAC THENL
     [UNDISCH_TAC `h * h + r * r = &1` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
      UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (t - r) * (b + A * c + B * s)`; `&0 <= (r - s) * (b + A * d + B * t)`;
    `&0 <= A * ((t - s) * h - ((t - r) * c + (r - s) * d))`;
    `&0 <= (t - s) * (b + A * h + B * r)`] THEN
  NLIN_TAC []);;

(* Lean: increasing *)
let CCUCC_INCREASING = prove
 (`forall c s d t A B.
     &0 < c /\ &0 <= d /\ c pow 2 + s pow 2 = &1 /\ d pow 2 + t pow 2 = &1 /\
     &0 <= s /\ &0 <= t /\ t <= s /\ &0 <= A /\ &0 <= B /\ &0 <= B * c - A * s
     ==> A * d + B * t <= A * c + B * s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] CCUCC_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  NLIN_FACTS_TAC []
   [`&0 <= B * (d - c)`; `&0 <= A * (s - t)`;
    `&0 <= B * (c + d) - A * (s + t)`;
    `&0 <= (s - t) * (B * (c + d) - A * (s + t))`;
    `&0 <= (c + d) * ((A * c + B * s) - (A * d + B * t))`] THEN
  NLIN_TAC []);;

(* Lean: decreasing *)
let CCUCC_DECREASING = prove
 (`forall c s d t A B.
     &0 < c /\ &0 <= d /\ c pow 2 + s pow 2 = &1 /\ d pow 2 + t pow 2 = &1 /\
     &0 <= s /\ &0 <= t /\ s <= t /\ &0 <= A /\ &0 <= B /\ &0 <= A * s - B * c
     ==> A * d + B * t <= A * c + B * s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CCUCC_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  NLIN_FACTS_TAC []
   [`&0 <= A * (t - s)`; `&0 <= B * (c - d)`;
    `&0 <= A * (s + t) - B * (c + d)`;
    `&0 <= (t - s) * (A * (s + t) - B * (c + d))`;
    `&0 <= (c + d) * ((A * c + B * s) - (A * d + B * t))`] THEN
  NLIN_TAC []);;
