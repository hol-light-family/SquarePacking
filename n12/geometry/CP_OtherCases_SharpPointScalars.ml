(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SharpPointScalars.lean              *)
(* (namespace N12Compact.Completion.OtherCases.SharpPointScalars).          *)
(* Exact projection margins for the shared sharp bar point.                 *)
(* C1092WallProfileScalars.half / quarter_data: C1092WPS_half /             *)
(* C1092WPS_QUARTER_DATA; CanonicalProjection.before / after: CCCP_BEFORE / *)
(* CCCP_AFTER.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;

let OCSPS_QD_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC];;

(* Lean: half_strict *)
let OCSPS_HALF_STRICT = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c ==> C1092WPS_half c s < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092WPS_half] THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Lean: half_upper *)
let OCSPS_HALF_UPPER = prove
 (`forall c s k. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ &1 < c + k * s
           ==> C1092WPS_half c s < k`,
  REPEAT STRIP_TAC THEN OCSPS_QD_TAC THEN
  ABBREV_TAC `h = C1092WPS_half c s` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `h * (&1 + c) = s` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (&1 + h pow 2) * (c + k * s - &1) /\ &0 <= h * (h - k)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_POW_2] THEN
      MP_TAC(SPEC `h:real` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `k * ((&1 + h pow 2) * s) = k * (&2 * h)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let t = concl th in is_eq t && not(is_var(lhs t))))) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    let t = concl th in not(is_eq t))) THEN
  REAL_ARITH_TAC);;

(* Lean: half_lower *)
let OCSPS_HALF_LOWER = prove
 (`forall c s a. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\ &1 < a * c + s
           ==> &1 - a < (&1 + a) * C1092WPS_half c s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSPS_HALF_STRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN OCSPS_QD_TAC THEN
  ABBREV_TAC `h = C1092WPS_half c s` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (&1 + h pow 2) * (a * c + s - &1) /\
                &0 <= (&1 - h) * ((&1 - a) - (&1 + a) * h)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_POW_2] THEN
      MP_TAC(SPEC `h:real` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `a * ((&1 + h pow 2) * c) = a * (&1 - h pow 2)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let t = concl th in is_eq t && not(is_var(lhs t))))) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    let t = concl th in not(is_eq t))) THEN
  REAL_ARITH_TAC);;

(* Lean: cross_identity (private) *)
let OCSPS_CROSS_IDENTITY = prove
 (`forall c s c0 s0 k. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
     (&1 + k pow 2) * c0 = &1 - k pow 2 /\ (&1 + k pow 2) * s0 = &2 * k
     ==> (&1 + C1092WPS_half c s pow 2) * (&1 + k pow 2) * (s0 * c - c0 * s) =
         &2 * (k - C1092WPS_half c s) * (&1 + k * C1092WPS_half c s)`,
  REPEAT STRIP_TAC THEN OCSPS_QD_TAC THEN
  ABBREV_TAC `h = C1092WPS_half c s` THEN
  SUBGOAL_THEN `(&1 + h pow 2) * (&1 + k pow 2) * (s0 * c - c0 * s) =
     ((&1 + k pow 2) * s0) * ((&1 + h pow 2) * c) -
     ((&1 + k pow 2) * c0) * ((&1 + h pow 2) * s)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let OCSPS_SCALE_POS = prove
 (`forall h k. &0 < (&1 + h pow 2) * (&1 + k pow 2)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[REAL_POW_2] THEN
  MP_TAC(SPEC `h:real` REAL_LE_SQUARE) THEN MP_TAC(SPEC `k:real` REAL_LE_SQUARE) THEN
  REAL_ARITH_TAC);;

(* Lean: half_before *)
let OCSPS_HALF_BEFORE = prove
 (`forall c s c0 s0 k. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &0 <= k /\
     (&1 + k pow 2) * c0 = &1 - k pow 2 /\ (&1 + k pow 2) * s0 = &2 * k /\
     C1092WPS_half c s <= k
     ==> c0 * s <= s0 * c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `c0:real`; `s0:real`; `k:real`] OCSPS_CROSS_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN OCSPS_QD_TAC THEN
  ABBREV_TAC `h = C1092WPS_half c s` THEN
  SUBGOAL_THEN `&0 <= (&2 * (k - h)) * (&1 + k * h)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`k:real`; `h:real`] REAL_LE_MUL) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`s0 * c - c0 * s`; `(&1 + h pow 2) * (&1 + k pow 2)`]
    (CONJUNCT1 C1092WPS_CANCEL)) THEN
  REWRITE_TAC[OCSPS_SCALE_POS] THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `s0 * c - c0 * s`)) (concl th))) THEN
    UNDISCH_TAC `&0 <= (&2 * (k - h)) * (&1 + k * h)` THEN
    REWRITE_TAC[REAL_MUL_AC] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: half_after *)
let OCSPS_HALF_AFTER = prove
 (`forall c s c0 s0 k. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &0 <= k /\
     (&1 + k pow 2) * c0 = &1 - k pow 2 /\ (&1 + k pow 2) * s0 = &2 * k /\
     k <= C1092WPS_half c s
     ==> s0 * c <= c0 * s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `c0:real`; `s0:real`; `k:real`] OCSPS_CROSS_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN OCSPS_QD_TAC THEN
  ABBREV_TAC `h = C1092WPS_half c s` THEN
  SUBGOAL_THEN `&0 <= (&2 * (h - k)) * (&1 + k * h)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`k:real`; `h:real`] REAL_LE_MUL) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`c0 * s - s0 * c`; `(&1 + h pow 2) * (&1 + k pow 2)`]
    (CONJUNCT1 C1092WPS_CANCEL)) THEN
  REWRITE_TAC[OCSPS_SCALE_POS] THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `s0 * c - c0 * s`)) (concl th))) THEN
    UNDISCH_TAC `&0 <= (&2 * (h - k)) * (&1 + k * h)` THEN
    REWRITE_TAC[REAL_MUL_AC] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: arc *)
let OCSPS_ARC = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1
         ==> &1 + &413 / &500 * c * s < c + s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c + s` ASSUME_TAC THENL
   [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c + s <= &99 / &70` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&99 / &70 - (c + s)) * ((c + s) - &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < c * s` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
  REAL_ARITH_TAC);;

(* projection step: half bound -> cross comparison -> CanonicalProjection *)
let OCSPS_PROJ_TAC halfth bound crossth projth c0 s0 k a b =
  MP_TAC(SPECL [`c:real`; `s:real`; c0; s0; k] crossth) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) THEN
    TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    MP_TAC halfth THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; c0; s0; a; b] projth) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN REAL_ARITH_TAC;;

(* Lean: outward_short_u *)
let OCSPS_OUTWARD_SHORT_U = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\
         &1 < c + &143 / &500 * s
         ==> &27 / &50 * c + s < &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&143 / &500`] OCSPS_HALF_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OCSPS_PROJ_TAC TRUTH () OCSPS_HALF_BEFORE CCCP_BEFORE
    `&229551 / &270449` `&143000 / &270449` `&143 / &500` `&27 / &50` `&1`);;

(* Lean: outward_lower_u *)
let OCSPS_OUTWARD_LOWER_U = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\
         &1 < c + &143 / &500 * s
         ==> &19 / &40 * c + &9 / &8 * s < &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&143 / &500`] OCSPS_HALF_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OCSPS_PROJ_TAC TRUTH () OCSPS_HALF_BEFORE CCCP_BEFORE
    `&229551 / &270449` `&143000 / &270449` `&143 / &500` `&19 / &40` `&9 / &8`);;

(* Lean: outward_lower_v *)
let OCSPS_OUTWARD_LOWER_V = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &1 < &37 / &50 * c + s
         ==> &9 / &8 * c - &11 / &40 * s < &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&37 / &50`] OCSPS_HALF_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OCSPS_PROJ_TAC TRUTH () OCSPS_HALF_AFTER CCCP_AFTER
    `&3700 / &3869` `&1131 / &3869` `&13 / &87` `&9 / &8` `--(&11 / &40)`);;

(* Lean: upper_lower_v *)
let OCSPS_UPPER_LOWER_V = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &1 < &11 / &25 * c + s
         ==> &7 / &8 * c + &21 / &40 * s < &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&11 / &25`] OCSPS_HALF_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OCSPS_PROJ_TAC TRUTH () OCSPS_HALF_AFTER CCCP_AFTER
    `&275 / &373` `&252 / &373` `&7 / &18` `&7 / &8` `&21 / &40`);;
