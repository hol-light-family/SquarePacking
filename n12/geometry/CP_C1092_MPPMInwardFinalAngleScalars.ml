(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalAngleScalars.lean          *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  Endpoint and coefficient    *)
(* norms of CENTERED-NEGATIVE-INWARD-ANGLE.  Normal: c977cc_normal; half /   *)
(* quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA; half_cross:          *)
(* C1092MIFE_HALF_CROSS; coordinates_after: C1092MIFSS_COORDINATES_AFTER;    *)
(* centeredD / capB / capR / centered_D_bounds / dot_strict:                 *)
(* c1092ifcs_* / C1092IFCS_*; CanonicalProjection.before: CCCP_BEFORE.       *)
(* Tag C1092IFAS_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCapScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalEndpoints.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessorScalars.ml";;

(* Lean: canonical_half_bounds *)
let C1092IFAS_CANONICAL_HALF_BOUNDS = prove
 (`forall c s. c977cc_normal c s
     ==> &0 <= C1092WPS_half c s /\ C1092WPS_half c s <= &5 / &12`,
  MATCH_ACCEPT_TAC C1092IFCS_HALF_BOUNDS);;

(* Lean: angle_endpoint *)
let C1092IFAS_ANGLE_ENDPOINT = prove
 (`forall c s. c977cc_normal c s /\ &21 / &100 <= C1092WPS_half c s
     ==> c <= &9559 / &10441 /\ (&7 / &16) * c <= s /\ (&2 / &5) * c <= s /\
         &13 / &10 < c + s /\ &0 < &1 - (&543 / &500) * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal (&9559 / &10441) (&4200 / &10441)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half (&9559 / &10441) (&4200 / &10441) = &21 / &100`
  ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`&9559 / &10441`; `&4200 / &10441`; `c:real`; `s:real`]
    C1092MIFE_HALF_CROSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&9559 / &10441`; `&4200 / &10441`]
    C1092MIFSS_COORDINATES_AFTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= (s - &4200 / &10441) * (c + &9559 / &10441 - s - &4200 / &10441)` THEN
  SUBGOAL_THEN `&0 <= (c + &9559 / &10441) * (c + s - &13759 / &10441)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&13759 / &10441 <= c + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092PRS_PROD `&0 < (c + &9559 / &10441) * (&13759 / &10441 - (c + s))` THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* positivity of the printed quartic on [21/100, 5/12] (chord argument) *)
let C1092IFAS_ANGLE_QUARTIC = prove
 (`forall x. &21 / &100 <= x /\ x <= &5 / &12
     ==> &0 < --(&1189749) * x pow 4 + &2308040 * x pow 3 - &2275898 * x pow 2 +
              &863960 * x - &49749`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `--(&1189749) * (x pow 2 + (&21 / &100 + &5 / &12) * x + (&21 / &100) pow 2 +
                    (&21 / &100) * (&5 / &12) + (&5 / &12) pow 2) +
    &2308040 * (x + &21 / &100 + &5 / &12) - &2275898 < &0` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (x - &21 / &100) * (&5 / &12 - x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: angle_norm *)
let C1092IFAS_ANGLE_NORM = prove
 (`forall c s. c977cc_normal c s /\ &21 / &100 <= C1092WPS_half c s
     ==> c1092ifcs_capB c s (&0) pow 2 + c1092ifcs_capR c s (&0) pow 2 < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFCS_HALF_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  MP_TAC(SPEC `x:real` C1092IFAS_ANGLE_QUARTIC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(&250000 * (&1 + x pow 2) pow 2) *
    (&1 - c1092ifcs_capB c s (&0) pow 2 - c1092ifcs_capR c s (&0) pow 2) =
    --(&1189749) * x pow 4 + &2308040 * x pow 3 - &2275898 * x pow 2 +
    &863960 * x - &49749` ASSUME_TAC THENL
   [REWRITE_TAC[c1092ifcs_capB; c1092ifcs_capR; c1092ifcs_centeredD] THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &250000 * (&1 + x pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN
      MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < &1 - c1092ifcs_capB c s (&0) pow 2 - c1092ifcs_capR c s (&0) pow 2`
  MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MP_TAC(SPECL [`&250000 * (&1 + x pow 2) pow 2`;
    `&1 - c1092ifcs_capB c s (&0) pow 2 - c1092ifcs_capR c s (&0) pow 2`]
    (CONJUNCT1 REAL_LT_MUL_EQ)) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: angle_own_positive *)
let C1092IFAS_ANGLE_OWN_POSITIVE = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &21 / &100 <= C1092WPS_half c s
     ==> &0 < &1 - (&543 / &500) * b - r + (c * r + s * b) * c1092ifcs_centeredD c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFAS_ANGLE_NORM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `c1092ifcs_capB c s (&0)`;
                `c1092ifcs_capR c s (&0)`; `&1`] C1092IFCS_DOT_STRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_ONE; REAL_LT_01] THEN
    ASM_MESON_TAC[c977cc_normal]; ALL_TAC] THEN
  REWRITE_TAC[c1092ifcs_capB; c1092ifcs_capR] THEN REAL_ARITH_TAC);;

(* Lean: angle_left *)
let C1092IFAS_ANGLE_LEFT = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &21 / &100 <= C1092WPS_half c s
     ==> &0 < &1 - b - r + (c * b + s * r) * c1092ifcs_centeredD c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFCS_CENTERED_D_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFAS_ANGLE_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `&1 - c * c1092ifcs_centeredD c s`;
                `&1 - s * c1092ifcs_centeredD c s`; `&1`] C1092IFCS_DOT_STRICT) THEN
  C1092PRS_NORMAL_TAC THEN
  ABBREV_TAC `D = c1092ifcs_centeredD c s` THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_ONE; REAL_LT_01] THEN
    C1092PRS_PROD `&0 <= D * (c + s - &13 / &10)` THEN
    C1092PRS_PROD `&0 <= (D - &27 / &50) * --(D + &27 / &50 - &13 / &5)` THEN
    SUBGOAL_THEN `(&1 - c * D) pow 2 + (&1 - s * D) pow 2 = &2 - &2 * (c + s) * D + D pow 2`
      ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: angle_right_before *)
let C1092IFAS_ANGLE_RIGHT_BEFORE = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &21 / &100 <= C1092WPS_half c s /\
             c * r <= s * b
     ==> &0 < &1 - (&543 / &500) * b + (s * b - c * r) * c1092ifcs_centeredD c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFCS_CENTERED_D_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFAS_ANGLE_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `c1092ifcs_centeredD c s = &1 - (&7 / &50) * c - s / &2` ASSUME_TAC THENL
   [REWRITE_TAC[c1092ifcs_centeredD]; ALL_TAC] THEN
  ABBREV_TAC `D = c1092ifcs_centeredD c s` THEN
  SUBGOAL_THEN
   `&1 - (&543 / &500) * b + (s * b - c * r) * D =
    &1 - ((&543 / &500 - s * D) * b + (c * D) * r)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s <= &1 / &2` THENL
   [SUBGOAL_THEN `(c * D) * c - (&543 / &500 - s * D) * s = D - (&543 / &500) * s`
      ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MP_TAC(SPECL [`b:real`; `r:real`; `c:real`; `s:real`;
                  `&543 / &500 - s * D`; `c * D`] CCCP_BEFORE) THEN
    SUBGOAL_THEN `(&543 / &500 - s * D) * c + (c * D) * s = (&543 / &500) * c` ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN RASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN RASM_ARITH_TAC;
    MP_TAC(SPECL [`b:real`; `r:real`; `&543 / &500 - s * D`; `c * D`; `&1`]
      C1092IFCS_DOT_STRICT) THEN
    ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_LT_01] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `D <= &33 / &50` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    C1092PRS_PROD `&0 <= (D - &27 / &50) * (&33 / &50 - D)` THEN
    C1092PRS_PROD `&0 <= D * (s - &1 / &2)` THEN
    SUBGOAL_THEN `(&543 / &500 - s * D) pow 2 + (c * D) pow 2 =
                  (&543 / &500) pow 2 - (&543 / &250) * s * D + D pow 2` ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]);;
