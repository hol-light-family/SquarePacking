(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortWallAllowance.lean                  *)
(* (N12Compact.C1092ShortWallAllowance).  The cubic allowance compared over  *)
(* every first-quadrant top-wall orientation.                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShortWallScalars.ml";;

let C1092SWA_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SWA_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWA_LIN_TAC; DISCH_TAC];;

(* Lean: quadrant_bounds (private) *)
let C1092SWA_QUADRANT_BOUNDS = prove
 (`forall r t. &0 <= r /\ &0 <= t /\ r pow 2 + t pow 2 = &1
         ==> r <= &1 /\ t <= &1 /\ &1 <= r + t /\ r + t <= &3 / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  C1092SWA_LE_MUL_TAC `r:real` `t:real` THEN
  REPEAT CONJ_TAC THEN
  NLIN_TAC [SQ_NONNEG `r:real`; SQ_NONNEG `t:real`; SQ_NONNEG `r - t`;
            SQ_NONNEG `r + t - &3 / &2`]);;

(* helper: 1 - d <= k on the unit circle quadrant *)
let C1092SWA_DEFECT = prove
 (`forall d k. &0 <= d /\ &0 <= k /\ d pow 2 + k pow 2 = &1 ==> &1 - d <= k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092SWA_LE_MUL_TAC `d:real` `k:real` THEN
  NLIN_FACTS_TAC [] [`&0 < (&1 - d - k) * (&1 + d + k)`] THEN C1092SWA_LIN_TAC);;

(* Lean: relative_bounds (private) *)
let C1092SWA_RELATIVE_BOUNDS = prove
 (`forall c s r t. c977cc_normal c s /\ &0 <= r /\ &0 <= t /\ r pow 2 + t pow 2 = &1
             ==> &0 <= c * r + s * t /\ c * r + s * t <= &1 /\
                 (c * r + s * t) pow 2 + (c * t - s * r) pow 2 = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  SUBGOAL_THEN `(c * r + s * t) pow 2 + (c * t - s * r) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `r pow 2 + t pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092SWA_LE_MUL_TAC `c:real` `r:real` THEN C1092SWA_LE_MUL_TAC `s:real` `t:real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [C1092SWA_LIN_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    can (find_term ((=) `c * t - s * r`)) (concl th) ||
    concl th = `&0 <= c * r` || concl th = `&0 <= s * t`)) THEN
  SPEC_TAC(`c * t - s * r`,`k:real`) THEN SPEC_TAC(`c * r + s * t`,`d:real`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_TAC [SQ_NONNEG `k:real`; SQ_NONNEG `d - &1`]);;

(* Lean: positive_order (private) *)
let C1092SWA_POSITIVE_ORDER = prove
 (`forall c s r t. c977cc_normal c s /\ &0 <= r /\ &0 <= t /\ r pow 2 + t pow 2 = &1 /\
             &0 <= c * t - s * r
             ==> r <= c /\ s <= t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092SWA_LE_MUL_TAC `c:real` `t:real` THEN C1092SWA_LE_MUL_TAC `s:real` `r:real` THEN
  C1092SWA_LE_MUL_TAC `c * t - s * r` `c * t + s * r` THEN
  SUBGOAL_THEN `(c * t - s * r) * (c * t + s * r) = t * t - s * s` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `r * r + t * t = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `s <= t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (s - t) * (s + t)`] THEN C1092SWA_LIN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < (r - c) * (r + c)`] THEN
  C1092SWA_LE_MUL_TAC `t - s` `t + s` THEN C1092SWA_LIN_TAC);;

(* Lean: above *)
let C1092SWA_ABOVE = prove
 (`forall c s r t. c977cc_normal c s /\ &4 * s <= c /\ &0 <= r /\ &0 <= t /\
             r pow 2 + t pow 2 = &1 /\ &0 <= c * t - s * r
             ==> C1092SWS_allowance r t <=
                 (c * r + s * t) * C1092SWS_allowance c s + (&7 / &20) * (c * t - s * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_NARROW_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_ALLOWANCE_BOUNDS) THEN
  MP_TAC(SPECL [`r:real`; `t:real`] C1092SWA_QUADRANT_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `t:real`] C1092SWA_RELATIVE_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `t:real`] C1092SWA_POSITIVE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  MP_TAC(SPECL [`c * r + s * t`; `c * t - s * r`] C1092SWA_DEFECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c - r = c * (&1 - (c * r + s * t)) + s * (c * t - s * r) /\
                t - s = c * (c * t - s * r) - s * (&1 - (c * r + s * t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  C1092SWA_LE_MUL_TAC `c:real` `(c * t - s * r) - (&1 - (c * r + s * t))` THEN
  C1092SWA_LE_MUL_TAC `c * t - s * r` `&5 / &4 - (c + s)` THEN
  C1092SWA_LE_MUL_TAC `s:real` `&1 - (c * r + s * t)` THEN
  C1092SWA_LE_MUL_TAC `c * t - s * r` `&1 - c` THEN
  C1092SWA_LE_MUL_TAC `c - r` `&5 / &2 - r - c - t` THEN
  C1092SWA_LE_MUL_TAC `t - s` `&1 / &25 - (&1 - c)` THEN
  C1092SWA_LE_MUL_TAC `C1092SWS_allowance c s` `(c * t - s * r) - (&1 - (c * r + s * t))` THEN
  C1092SWA_LE_MUL_TAC `c * t - s * r` `&1 / &200 - C1092SWS_allowance c s` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092SWS_allowance]) THEN
  REWRITE_TAC[C1092SWS_allowance] THEN C1092SWA_LIN_TAC);;

(* Lean: below *)
let C1092SWA_BELOW = prove
 (`forall c s r t. c977cc_normal c s /\ &4 * s <= c /\ &0 <= r /\ &0 <= t /\
             r pow 2 + t pow 2 = &1 /\ c * t - s * r <= &0
             ==> C1092SWS_allowance r t <=
                 (c * r + s * t) * C1092SWS_allowance c s - (c * t - s * r) / &200`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_NARROW_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_ALLOWANCE_BOUNDS) THEN
  MP_TAC(SPECL [`r:real`; `t:real`] C1092SWA_QUADRANT_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `t:real`] C1092SWA_RELATIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  C1092SWA_LE_MUL_TAC `s:real` `r:real` THEN C1092SWA_LE_MUL_TAC `c:real` `t:real` THEN
  C1092SWA_LE_MUL_TAC `s * r - c * t` `s * r + c * t` THEN
  SUBGOAL_THEN `(s * r - c * t) * (s * r + c * t) = s * s - t * t /\
                (c + r) * (c + s - r - t) = (s - t) * (c + r - s - t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    UNDISCH_TAC `r pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `t <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (t - s) * (t + s)`] THEN C1092SWA_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c <= r` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092SWA_LE_MUL_TAC `s - t` `s + t` THEN
    NLIN_FACTS_TAC [] [`&0 < (c - r) * (c + r)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092SWA_LIN_TAC;
    ALL_TAC] THEN
  C1092SWA_LE_MUL_TAC `s - t` `c + r - s - t` THEN
  SUBGOAL_THEN `r + t <= c + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (c + r) * (r + t - (c + s))`] THEN C1092SWA_LIN_TAC;
    ALL_TAC] THEN
  C1092SWA_LE_MUL_TAC `&1 - c` `(c + s - &1) - (r + t - &1)` THEN
  C1092SWA_LE_MUL_TAC `r + t - &1` `(&1 - c) - (&1 - r)` THEN
  MP_TAC(SPECL [`c * r + s * t`; `--(c * t - s * r)`] C1092SWA_DEFECT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C1092SWA_LIN_TAC; C1092SWA_LIN_TAC;
      UNDISCH_TAC `(c * r + s * t) pow 2 + (c * t - s * r) pow 2 = &1` THEN
      CONV_TAC REAL_RING];
    DISCH_TAC] THEN
  C1092SWA_LE_MUL_TAC `C1092SWS_allowance c s` `--(c * t - s * r) - (&1 - (c * r + s * t))` THEN
  C1092SWA_LE_MUL_TAC `--(c * t - s * r)` `&1 / &200 - C1092SWS_allowance c s` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092SWS_allowance]) THEN
  REWRITE_TAC[C1092SWS_allowance] THEN C1092SWA_LIN_TAC);;
