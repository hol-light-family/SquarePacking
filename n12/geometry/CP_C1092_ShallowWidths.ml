(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShallowWidths.lean                        *)
(* (N12Compact.C1092ShallowWidths).  The two square-width bounds used by the *)
(* shallow wall-order theorem.  Normal: c977cc_normal.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

let C1092SW_NONNEG_OF_MUL = prove
 (`forall k p. &0 < k /\ &0 <= k * p ==> &0 <= p`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: arc_chord (private) *)
let C1092SW_ARC_CHORD = prove
 (`forall c s h t A B.
     &0 <= c /\ &0 <= s /\ &0 <= h /\ &0 <= t /\
     c pow 2 + s pow 2 = &1 /\ h pow 2 + t pow 2 = &1 /\
     &0 <= A /\ &0 <= c * t - s * h /\ A * c <= B * (&1 + s)
     ==> A <= A * (c * h + s * t) + B * (c * t - s * h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCT_PROD_TAC `c:real` `h:real` THEN PCT_PROD_TAC `s:real` `t:real` THEN
  SUBGOAL_THEN `t <= &1` ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `h:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `(c * h + s * t) pow 2 + (c * t - s * h) pow 2 = &1 /\
                c * (&1 + (c * h + s * t)) - (c * t - s * h) * (&1 + s) =
                c * (&1 - t) + h * (&1 + s)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
   UNDISCH_TAC `h pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCT_PROD_TAC `c:real` `&1 - t` THEN PCT_PROD_TAC `h:real` `&1 + s` THEN
  PCT_PROD_TAC `B * (&1 + s) - A * c` `&1 + (c * h + s * t)` THEN
  PCT_PROD_TAC `A:real` `c * (&1 + (c * h + s * t)) - (c * t - s * h) * (&1 + s)` THEN
  MP_TAC(SPECL [`&1 + s`; `B * (&1 + (c * h + s * t)) - A * (c * t - s * h)`]
    C1092SW_NONNEG_OF_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  PCT_PROD_TAC `c * t - s * h` `B * (&1 + (c * h + s * t)) - A * (c * t - s * h)` THEN
  SUBGOAL_THEN
   `(&1 + (c * h + s * t)) * (A * (c * h + s * t) + B * (c * t - s * h) - A) =
    (c * t - s * h) * (B * (&1 + (c * h + s * t)) - A * (c * t - s * h))` ASSUME_TAC THENL
  [UNDISCH_TAC `(c * h + s * t) pow 2 + (c * t - s * h) pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 + (c * h + s * t)`;
                `A * (c * h + s * t) + B * (c * t - s * h) - A`] C1092SW_NONNEG_OF_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: weighted (private) *)
let C1092SW_WEIGHTED = prove
 (`forall c s h t w.
     &0 <= c /\ &0 <= s /\ &0 <= h /\ &0 <= t /\
     c pow 2 + s pow 2 = &1 /\ h pow 2 + t pow 2 = &1 /\
     &0 <= &1 + w * (c + s) /\
     (&1 + w * (c + s)) * c <= (&1 + w * (c - s)) * (&1 + s) /\
     (&1 + w * (c + s)) * s <= (&1 + w * (s - c)) * (&1 + c)
     ==> &1 + w * (c + s) <= w * (h + t) + abs(c * t - s * h) + c * h + s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= c * t - s * h` THENL
  [MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `t:real`; `&1 + w * (c + s)`;
                 `&1 + w * (c - s)`] C1092SW_ARC_CHORD) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 + w * (c + s)) * (c * h + s * t) + (&1 + w * (c - s)) * (c * t - s * h) =
                 w * (h + t) + (c * t - s * h) + c * h + s * t` SUBST1_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`];
   MP_TAC(SPECL [`s:real`; `c:real`; `t:real`; `h:real`; `&1 + w * (c + s)`;
                 `&1 + w * (s - c)`] C1092SW_ARC_CHORD) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 + w * (c + s)) * (s * t + c * h) + (&1 + w * (s - c)) * (s * h - c * t) =
                 w * (h + t) - (c * t - s * h) + c * h + s * t` SUBST1_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> abs x = --x`] THEN REAL_ARITH_TAC]);;

(* Lean: positive_widths *)
let C1092SW_POSITIVE_WIDTHS = prove
 (`forall c s h t. c977cc_normal c s /\ &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1
     ==> &1 + c * (c + s) <= c * (h + t) + abs(c * t - s * h) + c * h + s * t /\
         &1 + s * (c + s) <= s * (h + t) + abs(c * t - s * h) + c * h + s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  PCT_PROD_TAC `&1 - c` `&1 - c + s` THEN PCT_PROD_TAC `s:real` `c + s - &1` THEN
  PCT_PROD_TAC `c:real` `c + s - &1` THEN PCT_PROD_TAC `&1 - s` `&1 - s + c` THEN
  PCT_PROD_TAC `c:real` `c + s:real` THEN PCT_PROD_TAC `s:real` `c + s:real` THEN
  SUBGOAL_THEN
   `(&1 + c * (c - s)) * (&1 + s) - (&1 + c * (c + s)) * c = (&1 - c) * (&1 - c + s) /\
    (&1 + c * (s - c)) * (&1 + c) - (&1 + c * (c + s)) * s = s * (c + s - &1) /\
    (&1 + s * (c - s)) * (&1 + s) - (&1 + s * (c + s)) * c = c * (c + s - &1) /\
    (&1 + s * (s - c)) * (&1 + c) - (&1 + s * (c + s)) * s = (&1 - s) * (&1 - s + c)`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC C1092SW_WEIGHTED THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: signed_widths *)
let C1092SW_SIGNED_WIDTHS = prove
 (`forall c s a b. c977cc_normal c s /\ a pow 2 + b pow 2 = &1
     ==> &1 + c * (c + s) <= c * (abs a + abs b) + abs(c * b - s * a) + abs(c * a + s * b) /\
         &1 + s * (c + s) <= s * (abs a + abs b) + abs(c * b - s * a) + abs(c * a + s * b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(ASSUME `c977cc_normal c s`) THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  let case h t ea eb =
    MP_TAC(SPECL [`c:real`; `s:real`; h; t] C1092SW_POSITIVE_WIDTHS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
                    ALL_TAC] THEN
    PCT_PROD_TAC `c:real` ea THEN PCT_PROD_TAC `s:real` ea THEN
    PCT_PROD_TAC `c:real` eb THEN PCT_PROD_TAC `s:real` eb THEN
    RASM_ARITH_TAC in
  ASM_CASES_TAC `&0 <= a` THEN ASM_CASES_TAC `&0 <= b` THENL
  [case `a:real` `b:real` `a:real` `b:real`;
   case `--b` `a:real` `a:real` `--b`;
   case `b:real` `--a` `--a` `b:real`;
   case `--a` `--b` `--a` `--b`]);;
