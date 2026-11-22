(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/OuterArmScalars.lean                 *)
(* (namespace N12Compact.C1092MMMPOuterArmScalars).                          *)
(* The half-angle s / (1 + c) is C1092WPS_half with C1092WPS_QUARTER_DATA    *)
(* (WallProfileScalars); Normal: c977cc_normal.                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShortWallPenalty.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

let C1092MOAS_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)
    else NO_TAC));;

let C1092MOAS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN
     FIRST [ASM_REAL_ARITH_TAC; MATCH_ACCEPT_TAC REAL_LE_POW_2; NLIN_TAC []];
     ALL_TAC]) tms;;

let C1092MOAS_HALF_TAC c s w =
  let h = list_mk_comb(`C1092WPS_half`,[c;s]) in
  MP_TAC(SPECL [c; s] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (find_term ((=) h)) (concl th) then MP_TAC th else NO_TAC)) THEN
  SPEC_TAC(h,w) THEN GEN_TAC THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

let C1092MOAS_POSQ = prove
 (`forall z. &0 < &1 + z pow 2 /\ &0 < (&1 + z pow 2) pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]);;

(* Lean: endpoint *)
let C1092MOAS_ENDPOINT = prove
 (`forall c s. c977cc_normal c s ==> &0 <= ((&1 - c) pow 2 + s * (c - &4 / &5)) / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MOAS_NORMAL_TAC THEN
  C1092MOAS_HALF_TAC `c:real` `s:real` `z:real` THEN
  SUBGOAL_THEN `z <= &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MOAS_PROD_TAC [`&0 < (z - &1 / &2) * (&1 + c)`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + z pow 2) pow 2 * (((&1 - c) pow 2 + s * (c - &4 / &5)) / &2) =
                z * (&2 * z - &1) * (&5 * z pow 2 - &2 * z - &1) / &5` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&5 * z pow 2 - &2 * z - &1 <= &0` ASSUME_TAC THENL
   [C1092MOAS_PROD_TAC [`&0 <= z * (&1 / &2 - z)`] THEN NLIN_TAC []; ALL_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= (&1 - &2 * z) * --(&5 * z pow 2 - &2 * z - &1)`] THEN
  C1092MOAS_PROD_TAC [`&0 <= z * ((&1 - &2 * z) * --(&5 * z pow 2 - &2 * z - &1))`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC `z:real` C1092MOAS_POSQ) THEN STRIP_TAC THEN
  C1092MOAS_PROD_TAC
   [`&0 < (&1 + z pow 2) pow 2 * --(((&1 - c) pow 2 + s * (c - &4 / &5)) / &2)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: quadratic_monotone *)
let C1092MOAS_QUADRATIC_MONOTONE = prove
 (`forall c s h b. c977cc_normal c s /\ &0 <= h /\ &0 <= b /\ h pow 2 + b pow 2 = &1 /\
             h <= c /\ s <= b
     ==> (&1 - c) pow 2 + c * s <= (&1 - h) pow 2 + h * b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MOAS_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `h:real`] [`b <= &1`] THEN
  SUBGOAL_THEN `&0 <= (b + s) * (&2 - c - h - s) + h * (c + h)` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= &2 - c - h - s` THENL
     [C1092MOAS_PROD_TAC [`&0 <= (b + s) * (&2 - c - h - s)`; `&0 <= h * (c + h)`] THEN
      ASM_REAL_ARITH_TAC;
      C1092MOAS_PROD_TAC [`&0 <= (&2 - b - s) * --(&2 - c - h - s)`;
                          `&0 <= h * (c - &7 / &10)`] THEN
      NLIN_TAC [SQ_NONNEG `h - &13 / &20`]];
    ALL_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= (c - h) * ((b + s) * (&2 - c - h - s) + h * (c + h))`] THEN
  SUBGOAL_THEN `(b + s) * (((&1 - h) pow 2 + h * b) - ((&1 - c) pow 2 + c * s)) =
                (c - h) * ((b + s) * (&2 - c - h - s) + h * (c + h))` ASSUME_TAC THENL
   [UNDISCH_TAC `h pow 2 + b pow 2 = &1` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `b + s = &0` THENL
   [SUBGOAL_THEN `b = &0 /\ s = &0` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h = &1 /\ c = &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `h pow 2 + b pow 2 = &1` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN REPEAT CONJ_TAC THEN NLIN_TAC [];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092MOAS_PROD_TAC [`&0 < (b + s) * (((&1 - c) pow 2 + c * s) - ((&1 - h) pow 2 + h * b))`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: order_bounds (private) *)
let C1092MOAS_ORDER_BOUNDS = prove
 (`forall c s h b. c977cc_normal c s /\ &0 <= h /\ &0 <= b /\ h pow 2 + b pow 2 = &1 /\
             &0 <= s * h - c * b
     ==> c <= h /\ b <= s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MOAS_NORMAL_TAC THEN
  C1092MOAS_PROD_TAC [`&0 <= s * h`; `&0 <= c * b`] THEN
  C1092MOAS_PROD_TAC [`&0 <= (s * h - c * b) * (s * h + c * b)`] THEN
  SUBGOAL_THEN `(s * h) pow 2 - (c * b) pow 2 = s pow 2 - b pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `h pow 2 + b pow 2 = &1` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `b <= s` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MOAS_PROD_TAC [`&0 <= (s - b) * (s + b)`] THEN NLIN_TAC []);;

(* Lean: arc_correction (private) *)
let C1092MOAS_ARC_CORRECTION = prove
 (`forall c s h b. c977cc_normal c s /\ &0 < s /\ &0 <= h /\ &0 <= b /\
             h pow 2 + b pow 2 = &1 /\ &0 <= s * h - c * b
     ==> &0 <= s * ((&1 - h) pow 2 + h * b) - b * ((&1 - c) pow 2 + c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092MOAS_ORDER_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MOAS_NORMAL_TAC THEN
  C1092MOAS_HALF_TAC `c:real` `s:real` `z:real` THEN
  C1092MOAS_HALF_TAC `h:real` `b:real` `k:real` THEN
  SUBGOAL_THEN `s * z = &1 - c /\ b * k = &1 - h` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2`;
      UNDISCH_TAC `k * (&1 + h) = b` THEN UNDISCH_TAC `(&1 + k pow 2) * h = &1 - k pow 2`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `z <= &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MOAS_PROD_TAC [`&0 < (z - &1 / &2) * (&1 + c)`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k <= z` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MOAS_PROD_TAC [`&0 < (k - z) * (&1 + h)`; `&0 <= z * (h - c)`] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= z * k`; `&0 <= k * (&1 / &2 - z)`] THEN
  SUBGOAL_THEN `z * k <= &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= (z + k) * (&1 - z - k)`; `&0 <= (z * k) * (&1 - z * k)`] THEN
  C1092MOAS_PROD_TAC
   [`&0 <= (&2 * (z - k)) * ((z + k) * (&1 - z - k) + z * k * (&1 - z * k))`] THEN
  SUBGOAL_THEN
   `(&1 + z pow 2) * (&1 + k pow 2) * ((&1 - c) * (&1 - z) - (&1 - h) * (&1 - k)) =
    &2 * (z - k) * ((z + k) * (&1 - z - k) + z * k * (&1 - z * k))` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + k pow 2) * h = &1 - k pow 2` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - c) * (&1 - z) - (&1 - h) * (&1 - k)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPEC `z:real` C1092MOAS_POSQ) THEN MP_TAC(SPEC `k:real` C1092MOAS_POSQ) THEN
    REPEAT STRIP_TAC THEN
    C1092MOAS_PROD_TAC [`&0 < (&1 + z pow 2) * (&1 + k pow 2)`] THEN
    C1092MOAS_PROD_TAC
     [`&0 < ((&1 + z pow 2) * (&1 + k pow 2)) *
            --((&1 - c) * (&1 - z) - (&1 - h) * (&1 - k))`] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= s * b`] THEN
  C1092MOAS_PROD_TAC [`&0 <= (s * b) * ((&1 - c) * (&1 - z) - (&1 - h) * (&1 - k))`] THEN
  SUBGOAL_THEN
   `s * ((&1 - h) pow 2 + h * b) - b * ((&1 - c) pow 2 + c * s) =
    (s * b) * ((&1 - c) * (&1 - z) - (&1 - h) * (&1 - k))` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `s * z = &1 - c` THEN UNDISCH_TAC `b * k = &1 - h` THEN
    CONV_TAC REAL_RING; ASM_REWRITE_TAC[]]);;

(* Lean: first *)
let C1092MOAS_FIRST = prove
 (`forall c s h b. c977cc_normal c s /\ &0 < s /\ &0 <= h /\ &0 <= b /\
             h pow 2 + b pow 2 = &1 /\ &0 <= s * h - c * b
     ==> &0 <= &1 / &2 + h pow 2 / &2 + h * b / &2 +
               h * (c pow 2 - (&3 / &4) * c * s + s + (&7 / &20) * s pow 2 - &2) +
               b * ((&13 / &20) * c * s - (&2 / &5) * s pow 2 - c + (&7 / &20) * c pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092MOAS_ARC_CORRECTION) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MOAS_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C1092MOAS_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&13 / &20) * c - (&3 / &4) * s`;
                  SQ_NONNEG `(&3 / &4) * c + (&13 / &20) * s - &1`]
   [`(&3 / &4) * c + (&13 / &20) * s < &1`] THEN
  C1092MOAS_PROD_TAC [`&0 <= s * (&1 - (&3 / &4) * c - (&13 / &20) * s)`] THEN
  ABBREV_TAC `A = c pow 2 - (&3 / &4) * c * s + s + (&7 / &20) * s pow 2` THEN
  ABBREV_TAC `B = (&13 / &20) * c * s - (&2 / &5) * s pow 2 - c + (&7 / &20) * c pow 2` THEN
  SUBGOAL_THEN `&0 <= A - &1` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 + c pow 2 / &2 + c * s / &2 + c * (A - &2) + s * B =
                ((&1 - c) pow 2 + s * (c - &4 / &5)) / &2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= (s * h - c * b) * (A - &1)`;
                      `&0 <= b * (((&1 - c) pow 2 + s * (c - &4 / &5)) / &2)`] THEN
  SUBGOAL_THEN
   `s * (&1 / &2 + h pow 2 / &2 + h * b / &2 + h * (A - &2) + b * B) =
    (s * h - c * b) * (A - &1) +
    b * (((&1 - c) pow 2 + s * (c - &4 / &5)) / &2) +
    (s * ((&1 - h) pow 2 + h * b) - b * ((&1 - c) pow 2 + c * s)) / &2`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092MOAS_PROD_TAC
   [`&0 < s * --(&1 / &2 + h pow 2 / &2 + h * b / &2 + h * (A - &2) + b * B)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: second *)
let C1092MOAS_SECOND = prove
 (`forall c s h b. c977cc_normal c s /\ &0 <= h /\ &0 <= b /\
             h pow 2 + b pow 2 = &1 /\ s * h - c * b <= &0
     ==> &0 <= &1 / &2 + h pow 2 / &2 + h * b / &2 +
               h * (c pow 2 - (&2 / &5) * c * s - &2) +
               b * (c * s - (&2 / &5) * s pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MOAS_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o check (fun th -> concl th = `c977cc_normal c s`)) THEN
  C1092MOAS_NORMAL_TAC THEN
  C1092MOAS_PROD_TAC [`&0 <= c * b`; `&0 <= s * h`] THEN
  C1092MOAS_PROD_TAC [`&0 <= (c * b - s * h) * (c * b + s * h)`] THEN
  SUBGOAL_THEN `(c * b) pow 2 - (s * h) pow 2 = b pow 2 - s pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `h pow 2 + b pow 2 = &1` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `s <= b` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= (b - s) * (s + b)`] THEN
  SUBGOAL_THEN `h <= c` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092MOAS_QUADRATIC_MONOTONE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= c * s`; `&0 <= s * (c - (&2 / &5) * s)`] THEN
  SUBGOAL_THEN `c pow 2 - (&2 / &5) * c * s - &1 <= &0 /\
                &0 <= c * s - (&2 / &5) * s pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  C1092MOAS_PROD_TAC
   [`&0 <= (c - h) * --(c pow 2 - (&2 / &5) * c * s - &1)`;
    `&0 <= (b - s) * (c * s - (&2 / &5) * s pow 2)`] THEN
  SUBGOAL_THEN
   `(&1 - c) pow 2 / &2 + c * s / &2 + c * ((c pow 2 - (&2 / &5) * c * s) - &1) +
    s * (c * s - (&2 / &5) * s pow 2) = ((&1 - c) pow 2 + s * (c - &4 / &5)) / &2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
