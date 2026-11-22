(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardOuterFarScalars.lean           *)
(* (namespace N12Compact.C1092MPPMInwardOuterFar).  Exact whole-arc          *)
(* comparisons for the missing-center / center-owned outer-owned inward far  *)
(* endings.  Normal = c977cc_normal, half / quarter_data = C1092WPS_half /   *)
(* C1092WPS_QUARTER_DATA, missing_bounds = C1092ANAS_MISSING_BOUNDS,         *)
(* dot_le_one = C977CSB_DOT_LE_ONE.                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveAlternatingScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalScalars.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092MIOF_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   NLIN_TAC ~deg2:false []; ALL_TAC];;

let C1092MIOF_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: alpha (definition) *)
let c1092miof_alpha = new_definition
 `c1092miof_alpha (c:real) (s:real) = &1 - c + (&13 / &50) * s`;;

(* Lean: centralGap (definition) *)
let c1092miof_centralGap = new_definition
 `c1092miof_centralGap (c:real) (s:real) (d:real) (t:real) =
    c1092miof_alpha c s + (c * d + s * t) * (&1 - d - t) +
    (c * t - s * d) * (&1 - t + (&14 / &25) * d)`;;

(* Lean: recipientGap (definition) *)
let c1092miof_recipientGap = new_definition
 `c1092miof_recipientGap (eta:real) (c:real) (s:real) (d:real) (t:real) =
    &1 - d - t + (c * d + s * t) * c1092miof_alpha c s + (&1 - eta) * (c * t - s * d)`;;

(* Lean: cap_coordinates *)
let C1092MIOF_CAP_COORDINATES = prove
 (`forall c s m. c977cc_normal c s /\ &0 <= m /\ m <= &1 /\ C1092WPS_half c s <= m
     ==> &1 - m pow 2 <= (&1 + m pow 2) * c /\ (&1 + m pow 2) * s <= &2 * m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + x pow 2) * ((&1 + m pow 2) * c - (&1 - m pow 2)) =
                &2 * (m pow 2 - x pow 2) /\
                (&1 + x pow 2) * (&2 * m - (&1 + m pow 2) * s) =
                &2 * (m - x) * (&1 - m * x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  C1092MIOF_PROD `&0 <= (m - x) * (m + x)` THEN
  C1092MIOF_PROD `&0 <= m * (&1 - x)` THEN
  SUBGOAL_THEN `&0 <= &1 - m * x` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C1092MIOF_PROD `&0 <= (m - x) * (&1 - m * x)` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`&1 + x pow 2`; `(&1 + m pow 2) * c - (&1 - m pow 2)`] C1092MIOF_CANCEL);
    MP_TAC(SPECL [`&1 + x pow 2`; `&2 * m - (&1 + m pow 2) * s`] C1092MIOF_CANCEL)] THEN
  ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL [NLIN_TAC ~deg2:false []; REAL_ARITH_TAC]));;

(* Lean: far_coordinates *)
let C1092MIOF_FAR_COORDINATES = prove
 (`forall d t. c977cc_normal d t /\ &7 / &18 < C1092WPS_half d t
     ==> &252 / &373 < t /\ d < &275 / &373`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `d:real` `t:real` `z:real` THEN
  SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MIOF_PROD `&0 < (z - &7 / &18) * (z + &7 / &18)` THEN
  C1092MIOF_PROD `&0 < (z - &7 / &18) * (&1 - (&7 / &18) * z)` THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
   [C1092MIOF_PROD `&0 <= (&1 + z pow 2) * (&252 / &373 - t)`;
    C1092MIOF_PROD `&0 <= (&1 + z pow 2) * (d - &275 / &373)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: central_positive *)
let C1092MIOF_CENTRAL_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &7 / &18 < C1092WPS_half d t
     ==> &0 < c1092miof_centralGap c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MIOF_FAR_COORDINATES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092ANAS_MISSING_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; c1092anas_missingBounds] THEN STRIP_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `d * t <= &1 / &2` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `d - t:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 - d - t + (&11 / &25) * d * t < &81 / &100` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C1092MIOF_PROD `&0 <= (d - t) * (d + t - &141 / &100)` THEN
  SUBGOAL_THEN `d - t + &3 / &10 + (&11 / &25) * t pow 2 < &57 / &100` ASSUME_TAC THENL
   [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(&81 / &100) * c + (&57 / &100) * s < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MIOF_PROD `&0 <= ((&81 / &100) * c + (&57 / &100) * s - &1) *
                          ((&81 / &100) * c + (&57 / &100) * s + &1)` THEN
    NLIN_TAC [SQ_NONNEG `(&57 / &100) * c - (&81 / &100) * s`]; ALL_TAC] THEN
  C1092MIOF_PROD `&0 <= c * (&81 / &100 - (&2 - d - t + (&11 / &25) * d * t))` THEN
  C1092MIOF_PROD `&0 <= s * (&57 / &100 - (d - t + &3 / &10 + (&11 / &25) * t pow 2))` THEN
  SUBGOAL_THEN `c1092miof_centralGap c s d t =
      &1 - (&2 - d - t + (&11 / &25) * d * t) * c -
      (d - t + &3 / &10 + (&11 / &25) * t pow 2) * s` SUBST1_TAC THENL
   [REWRITE_TAC[c1092miof_centralGap; c1092miof_alpha] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: recipient_order *)
let C1092MIOF_RECIPIENT_ORDER = prove
 (`forall d t A B. c977cc_normal d t /\ &252 / &373 <= t /\ &0 <= A /\
     &0 <= (&252 / &373) * A - (&275 / &373) * B
     ==> A * d + B * t <= A * (&275 / &373) + B * (&252 / &373)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&275 / &373`; `&252 / &373`; `d:real`; `t:real`] C977CSB_DOT_LE_ONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  C1092MIOF_PROD `&0 <= A * (&1 - ((&275 / &373) * d + (&252 / &373) * t))` THEN
  C1092MIOF_PROD `&0 <= ((&252 / &373) * A - (&275 / &373) * B) * (t - &252 / &373)` THEN
  NLIN_TAC ~deg2:false []);;
