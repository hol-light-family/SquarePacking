(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalCapScalars.lean            *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  Full-domain predecessor     *)
(* margins of CENTERED-NEGATIVE-INWARD-H-CAP.  Normal: c977cc_normal;        *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA; f / g /       *)
(* fg_bounds: c1092mifs_f / c1092mifs_g / C1092MIFS_FG_BOUNDS;               *)
(* CanonicalProjection.before: CCCP_BEFORE.                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCenteredCaps.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessorScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;

let C1092IFCS_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: centeredD, capB, capR (definitions) *)
let c1092ifcs_centeredD = new_definition
 `c1092ifcs_centeredD (c:real) (s:real) = &1 - (&7 / &50) * c - s / &2`;;

let c1092ifcs_capB = new_definition
 `c1092ifcs_capB (c:real) (s:real) (eta:real) =
    &543 / &500 - s * c1092ifcs_centeredD c s - eta * c`;;

let c1092ifcs_capR = new_definition
 `c1092ifcs_capR (c:real) (s:real) (eta:real) =
    &1 - c * c1092ifcs_centeredD c s + eta * s`;;

(* Lean: centered_D_bounds *)
let C1092IFCS_CENTERED_D_BOUNDS = prove
 (`forall c s. c977cc_normal c s
     ==> &27 / &50 < c1092ifcs_centeredD c s /\ c1092ifcs_centeredD c s <= &43 / &50`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  REWRITE_TAC[c1092ifcs_centeredD] THEN C1092IFCS_LP_TAC);;

(* Lean: dot_strict *)
let C1092IFCS_DOT_STRICT = prove
 (`forall b r P Q K. b pow 2 + r pow 2 = &1 /\ &0 < K /\ P pow 2 + Q pow 2 < K pow 2
     ==> P * b + Q * r < K`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C1092NPP_NORM_LT THEN ASM_REWRITE_TAC[]);;

(* Lean: half_bounds (private) *)
let C1092IFCS_HALF_BOUNDS = prove
 (`forall c s. c977cc_normal c s
     ==> &0 <= C1092WPS_half c s /\ C1092WPS_half c s <= &5 / &12`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFCS_LP_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c s`,`x:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + x pow 2) * (c - s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC []);;

(* positivity of the printed quartic on [0,5/12] (chord argument) *)
let C1092IFCS_CAP_QUARTIC = prove
 (`forall x. &0 <= x /\ x <= &5 / &12
     ==> &0 < --(&1268221) * x pow 4 + &2172040 * x pow 3 - &2285146 * x pow 2 +
              &727960 * x + &19475`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `--(&1268221) * (x pow 2 + (&5 / &12) * x + (&5 / &12) pow 2) +
    &2172040 * (x + &5 / &12) - &2285146 < &0` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= x * (&5 / &12 - x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: cap_norm *)
let C1092IFCS_CAP_NORM = prove
 (`forall c s. c977cc_normal c s
     ==> c1092ifcs_capB c s (&17 / &125) pow 2 + c1092ifcs_capR c s (&17 / &125) pow 2 < &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFCS_HALF_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  MP_TAC(SPEC `x:real` C1092IFCS_CAP_QUARTIC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(&250000 * (&1 + x pow 2) pow 2) *
    (&1 - c1092ifcs_capB c s (&17 / &125) pow 2 - c1092ifcs_capR c s (&17 / &125) pow 2) =
    --(&1268221) * x pow 4 + &2172040 * x pow 3 - &2285146 * x pow 2 +
    &727960 * x + &19475` ASSUME_TAC THENL
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
   `&0 < &1 - c1092ifcs_capB c s (&17 / &125) pow 2 - c1092ifcs_capR c s (&17 / &125) pow 2`
  MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MP_TAC(SPECL [`&250000 * (&1 + x pow 2) pow 2`;
    `&1 - c1092ifcs_capB c s (&17 / &125) pow 2 - c1092ifcs_capR c s (&17 / &125) pow 2`]
    (CONJUNCT1 REAL_LT_MUL_EQ)) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: cap_own_positive *)
let C1092IFCS_CAP_OWN_POSITIVE = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r
     ==> &0 < &1 - (&543 / &500) * b - r + (c * r + s * b) * c1092ifcs_centeredD c s +
              (c * b - s * r) * (&17 / &125)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFCS_CAP_NORM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `c1092ifcs_capB c s (&17 / &125)`;
                `c1092ifcs_capR c s (&17 / &125)`; `&1`] C1092IFCS_DOT_STRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_ONE; REAL_LT_01] THEN
    ASM_MESON_TAC[c977cc_normal]; ALL_TAC] THEN
  REWRITE_TAC[c1092ifcs_capB; c1092ifcs_capR] THEN REAL_ARITH_TAC);;

(* Lean: cap_left_positive *)
let C1092IFCS_CAP_LEFT_POSITIVE = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r
     ==> &0 < &1 - b - r + (c * b + s * r) * c1092ifcs_centeredD c s +
              (c * r - s * b) * (&17 / &125)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFCS_CAP_NORM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFCS_CENTERED_D_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&43 / &1000 < c1092ifcs_capB c s (&17 / &125)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= c * (&1 - c1092ifcs_centeredD c s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c1092ifcs_centeredD c s <= &43 / &50` THEN
    UNDISCH_TAC `&27 / &50 < c1092ifcs_centeredD c s` THEN
    REWRITE_TAC[c1092ifcs_capB; c1092ifcs_centeredD] THEN
    REPEAT DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN
   `c1092ifcs_capR c s (&17 / &125) pow 2 +
    (c1092ifcs_capB c s (&17 / &125) - &43 / &500) pow 2 < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `&43 / &1000 < c1092ifcs_capB c s (&17 / &125)` THEN
    UNDISCH_TAC `c1092ifcs_capB c s (&17 / &125) pow 2 +
                 c1092ifcs_capR c s (&17 / &125) pow 2 < &1` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `c1092ifcs_capR c s (&17 / &125)`;
                `c1092ifcs_capB c s (&17 / &125) - &43 / &500`; `&1`]
    C1092IFCS_DOT_STRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_ONE; REAL_LT_01] THEN
    ASM_MESON_TAC[c977cc_normal]; ALL_TAC] THEN
  REWRITE_TAC[c1092ifcs_capB; c1092ifcs_capR] THEN REAL_ARITH_TAC);;

(* Lean: cap_left_before *)
let C1092IFCS_CAP_LEFT_BEFORE = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ c * r <= s * b
     ==> &0 < &1 - b - r + (c * b + s * r) * c1092ifcs_centeredD c s +
              (s * b - c * r) * (&1 - (&7 / &20) * (c - s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFCS_CENTERED_D_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  ABBREV_TAC `D = c1092ifcs_centeredD c s` THEN
  ABBREV_TAC `E = &1 - (&7 / &20) * (c - s)` THEN
  SUBGOAL_THEN `&0 < E` ASSUME_TAC THENL [EXPAND_TAC "E" THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - s * D + c * E) * c - (&1 - c * D - s * E) * s = c - s + E`
  ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - c * D - s * E) * c + (&1 - s * D + c * E) * s = c + s - D`
  ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `c:real`; `s:real`;
                `&1 - c * D - s * E`; `&1 - s * D + c * E`] CCCP_BEFORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&57 / &50`; `&3 / &2`; `&2`] C1092IFCS_DOT_STRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&1 - b - r + (c * b + s * r) * D + (s * b - c * r) * E =
    &1 - (&1 - c * D - s * E) * b - (&1 - s * D + c * E) * r` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "D" THEN
  UNDISCH_TAC `(&1 - c * D - s * E) * c + (&1 - s * D + c * E) * s = c + s - D` THEN
  EXPAND_TAC "D" THEN REWRITE_TAC[c1092ifcs_centeredD] THEN
  UNDISCH_TAC `(&57 / &50) * c + (&3 / &2) * s < &2` THEN
  UNDISCH_TAC
   `(&1 - c * D - s * E) * b + (&1 - s * D + c * E) * r <=
    (&1 - c * D - s * E) * c + (&1 - s * D + c * E) * s` THEN
  EXPAND_TAC "D" THEN REWRITE_TAC[c1092ifcs_centeredD] THEN
  REAL_ARITH_TAC);;

(* Lean: cap_f0 *)
let C1092IFCS_CAP_F0 = prove
 (`forall b r. c977cc_normal b r
     ==> (b + r - &1) pow 2 / &2 + (&43 / &500) * r pow 2 < &13 / &100 /\
         &0 <= r pow 2 + b - r - (&43 / &500) * b * r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `b + r <= &99 / &70` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `b - r:real`; SQ_NONNEG `b + r - &99 / &70`]; ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 <= &1 / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (b - r) * (b + r)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&99 / &70 - (b + r)) * (b + r - &1 + &29 / &70)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (b - r) * (&1 - (&43 / &500) * r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `r:real`]);;

(* Lean: cap_g0 *)
let C1092IFCS_CAP_G0 = prove
 (`forall b r. c977cc_normal b r /\ b + r < &29 / &25
     ==> &43 / &500 + (b + r - &1) pow 2 / &2 < &247 / &2500 /\ &0 <= r pow 2 + b - r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < (&29 / &25 - (b + r)) * (b + r - &1 + &4 / &25)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `r:real`]);;


(* Lean: cap_negative_fg *)
let C1092IFCS_CAP_NEGATIVE_FG = prove
 (`forall b r. c977cc_normal b r
     ==> (&43 / &500) * b pow 2 + c1092mifs_f b r < &17 / &125 /\
         &0 <= c1092mifs_g b r - (&43 / &500) * b * r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092MIFS_FG_BOUNDS) THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092IFCS_HALF_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `b:real` `r:real` `w:real` THEN
  SUBGOAL_THEN
   `(&500 * (&1 + w pow 2) pow 2) * (&17 / &125 - ((&43 / &500) * b pow 2 + c1092mifs_f b r)) =
    &16 / &27 + (&32 / &9) * (w - &1 / &3) +
    (w - &1 / &3) pow 2 * (&572 + &700 * (w - &1 / &3) - &975 * (w - &1 / &3) pow 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[c1092mifs_f] THEN
    UNDISCH_TAC `(&1 + w pow 2) * b = &1 - w pow 2` THEN
    UNDISCH_TAC `(&1 + w pow 2) * r = &2 * w` THEN
    UNDISCH_TAC `b pow 2 + r pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < &16 / &27 + (&32 / &9) * (w - &1 / &3) +
    (w - &1 / &3) pow 2 * (&572 + &700 * (w - &1 / &3) - &975 * (w - &1 / &3) pow 2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `-- &1 / &3 <= w - &1 / &3 /\ w - &1 / &3 <= &1 / &12` MP_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`w - &1 / &3`,`h:real`) THEN
    GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&691 / &3 <= &572 + &700 * h - &975 * h pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= (&1 / &3 - h) * (&1 / &3 + h)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= h pow 2 * ((&572 + &700 * h - &975 * h pow 2) - &691 / &3)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN RASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &16 / &27 + (&32 / &9) * h + (&691 / &3) * h pow 2` ASSUME_TAC THENL
     [NLIN_TAC [SQ_NONNEG `(&1382 / &3) * h + &32 / &9`]; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &500 * (&1 + w pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN
      MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &17 / &125 - ((&43 / &500) * b pow 2 + c1092mifs_f b r)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`&500 * (&1 + w pow 2) pow 2`;
      `&17 / &125 - ((&43 / &500) * b pow 2 + c1092mifs_f b r)`]
      (CONJUNCT1 REAL_LT_MUL_EQ)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r * (&1 - r / &2 - (&43 / &500) * b)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `r - r pow 2 / &2 <= c1092mifs_g b r` THEN
  REAL_ARITH_TAC);;
