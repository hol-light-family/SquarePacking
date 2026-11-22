(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointG10.lean    *)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointSupport),                   *)
(* MISSING-NEGATIVE-WALL-SCALARS section 4, all boundary orientations.       *)
(* Normal: c977cc_normal; Quarter, kC, deltaE, FC: c1092mncs_*;              *)
(* G10, G00, G10star: c1092mmncs_*; G10Scalars lemmas C1092MNG10S_*;         *)
(* FC_low/middle/high_cap: C1092NCCL_*; G00_lower: C1092MMNCC_G00_LOWER;     *)
(* large_sum: C1092MMNCE_LARGE_SUM; sine_order: C977CSB_SINE_ORDER.          *)
(* Tag C1092MMNG10_.                                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointG10Scalars.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointCentral.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointClamp.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092MMNG10_LIN = REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092MMNG10_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN C1092MMNG10_LIN; ALL_TAC];;

let C1092MMNG10_UNFOLD_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC));;

let C1092MMNG10_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092MMNG10_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC);;

(* Lean: before_of_lower (private) *)
let C1092MMNG10_BEFORE_OF_LOWER = prove
 (`forall d t h r. c977cc_normal d t /\ c1092mncs_quarter h r /\ r <= h
             ==> c1092mncs_deltaE d t h r <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MMNG10_NORMAL_TAC THEN C1092MMNG10_UNFOLD_TAC THEN
  C1092MMNG10_PROD `&0 <= t * (h - r)` THEN
  C1092MMNG10_PROD `&0 <= h * (d - t)` THEN
  REWRITE_TAC[c1092mncs_deltaE] THEN C1092MMNG10_LIN);;

(* Lean: low (private) *)
let C1092MMNG10_LOW = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &252 / &373 <= t /\ c1092mncs_quarter h r /\ r <= &3 / &5
     ==> &3 / &50 <= c1092mmncs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG10S_QUARTER_BOUNDS) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG10S_LOW_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MNG10S_RECIPIENT_BOUNDS) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG10S_LOW_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_LOW_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MMNG10_BEFORE_OF_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG10S_BEFORE_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MMNG10_NORMAL_TAC THEN C1092MMNG10_UNFOLD_TAC THEN
  C1092MMNG10_PROD `&0 <= t * ((--(&29 / &25) * h + (&22 / &25) * r) - c1092mncs_FC c s h r)` THEN
  C1092MMNG10_PROD `&0 <= (&1 - h) * (h + &4 / &25)` THEN
  C1092MMNG10_PROD `&0 <= r * (&47 / &25 - h)` THEN
  SUBGOAL_THEN `h * (h + r) - (&21 / &25) * h - (&47 / &25) * r <= &4 / &25` ASSUME_TAC THENL
   [C1092MMNG10_LIN; ALL_TAC] THEN
  C1092MMNG10_PROD `&0 <= (&3 / &4 - t) *
     (&4 / &25 - (h * (h + r) - (&21 / &25) * h - (&47 / &25) * r))` THEN
  C1092MMNG10_PROD `&0 <= (&3 / &4 - d) * r * (&36 / &25 - h - r)` THEN
  C1092MMNG10_LIN);;

(* Lean: middle (private) *)
let C1092MMNG10_MIDDLE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &252 / &373 <= t /\ c1092mncs_quarter h r /\ &3 / &5 <= r /\ r <= h
     ==> &47 / &1000 <= c1092mmncs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal h r` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092mncs_quarter h r` THEN
    REWRITE_TAC[c977cc_normal; c1092mncs_quarter; c1092mcs_quarter] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_MIDDLE_CAP) THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MMNCC_G00_LOWER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c1092mmncs_G10 c s d t h r - c1092mmncs_G00 h r d t h r =
                t * ((r - &1) - c1092mncs_FC c s h r)` ASSUME_TAC THENL
   [C1092MMNG10_UNFOLD_TAC THEN
    REWRITE_TAC[c1092mmncs_G10; c1092mmncs_G00; c1092mncs_width; c1092mncs_ell;
                c1092mncs_C0; c1092mncs_kE] THEN
    REWRITE_TAC[c1092mncs_kC; c1092mncs_deltaC; REAL_ARITH `h * r - r * h = &0`;
                REAL_ABS_0] THEN
    UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  C1092MMNG10_NORMAL_TAC THEN
  C1092MMNG10_PROD `&0 <= t * ((r - &1) - c1092mncs_FC c s h r)` THEN
  C1092MMNG10_LIN);;

(* Lean: high_before (private) *)
let C1092MMNG10_HIGH_BEFORE = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\
     &252 / &373 <= t /\ c1092mncs_quarter h r /\ h <= r /\
     c1092mncs_deltaE d t h r <= &0
     ==> &3 / &50 <= c1092mmncs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal r h` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092mncs_quarter h r` THEN
    REWRITE_TAC[c977cc_normal; c1092mncs_quarter; c1092mcs_quarter] THEN
    ASM_SIMP_TAC[REAL_ADD_SYM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`r:real`; `h:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG10S_QUARTER_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MNG10S_RECIPIENT_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_HIGH_CAP) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG10S_BEFORE_FORMULA) THEN
  MP_TAC(SPECL [`r:real`; `h:real`; `d:real`; `t:real`] C977CSB_SINE_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c1092mncs_deltaE d t h r <= &0` THEN
    REWRITE_TAC[c1092mncs_deltaE] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`r:real`; `h:real`] C1092MMNCE_LARGE_SUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C1092MMNG10_NORMAL_TAC THEN C1092MMNG10_UNFOLD_TAC THEN
  C1092MMNG10_PROD `&0 <= t * ((--h / &2 + (&9 / &100) * r) - c1092mncs_FC c s h r)` THEN
  C1092MMNG10_PROD `&0 <= h * (&3 / &2 - h - r)` THEN
  C1092MMNG10_PROD `&0 <= (&3 / &4 - t) * ((&109 / &100) * r - h * (h + r - &3 / &2))` THEN
  C1092MMNG10_PROD `&0 <= (&3 / &4 - d) * r * (&36 / &25 - h - r)` THEN
  C1092MMNG10_PROD `&0 <= h * (h + r - &141 / &100)` THEN
  C1092MMNG10_PROD `&0 <= r * (h + r - &141 / &100)` THEN
  C1092MMNG10_LIN);;

(* Lean: high_after (private) *)
let C1092MMNG10_HIGH_AFTER = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\
     &252 / &373 <= t /\ c1092mncs_quarter h r /\ h <= r /\
     &0 <= c1092mncs_deltaE d t h r
     ==> &3 / &50 <= c1092mmncs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG10S_QUARTER_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MNG10S_RECIPIENT_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_HIGH_CAP) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG10S_AFTER_FORMULA) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG10S_HIGH_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092MMNG10_NORMAL_TAC THEN C1092MMNG10_UNFOLD_TAC THEN
  C1092MMNG10_PROD `&0 <= t * ((--h / &2 + (&9 / &100) * r) - c1092mncs_FC c s h r)` THEN
  C1092MMNG10_PROD `&0 <= h * (&1 + r - &2 * h)` THEN
  SUBGOAL_THEN `&2 * (&1 - r) <= h` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= h - &2 * (&1 - r)` MP_TAC THENL
     [MATCH_MP_TAC C1092MMNG10_CANCEL THEN EXISTS_TAC `&1 + r` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(&1 + r) * (h - &2 * (&1 - r)) = h * (&1 + r - &2 * h)`
        SUBST1_TAC THENL
       [UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING;
        ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  C1092MMNG10_PROD `&0 <= h * (&1 - r)` THEN
  SUBGOAL_THEN `&1 + h * r - (&3 / &2) * h - (&109 / &100) * r <= &0` ASSUME_TAC THENL
   [C1092MMNG10_LIN; ALL_TAC] THEN
  C1092MMNG10_PROD `&0 <= (&3 / &4 - t) *
     --(&1 + h * r - (&3 / &2) * h - (&109 / &100) * r)` THEN
  C1092MMNG10_PROD `&0 <= (&3 / &4 - d) * r * (&36 / &25 - r)` THEN
  C1092MMNG10_LIN);;

(* Lean: G10_lower *)
let C1092MMNG10_G10_LOWER = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &252 / &373 <= t /\ c1092mncs_quarter h r
     ==> &47 / &1000 <= c1092mmncs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `r <= &3 / &5` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
      C1092MMNG10_LOW) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r <= h` THENL
   [MATCH_MP_TAC C1092MMNG10_MIDDLE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c1092mncs_deltaE d t h r` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
      C1092MMNG10_HIGH_AFTER);
    MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
      C1092MMNG10_HIGH_BEFORE)] THEN
  ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]));;

(* Lean: G10star_lower *)
let C1092MMNG10_G10STAR_LOWER = prove
 (`forall epsilon c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &252 / &373 <= t /\ c1092mncs_quarter h r /\ epsilon <= &43 / &500
     ==> &1 / &250 <= c1092mmncs_G10star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MMNG10_G10_LOWER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092MMNG10_NORMAL_TAC THEN C1092MMNG10_UNFOLD_TAC THEN
  SUBGOAL_THEN `&0 <= c1092mncs_kC c s h r` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_kC] THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c1092mncs_kC c s h r <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_kC] THEN
    MP_TAC(SPEC `c - h:real` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `s - r:real` REAL_LE_POW_2) THEN
    UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092MMNG10_PROD `&0 <= (c - s) * (c + s)` THEN
  C1092MMNG10_PROD `&0 <= (d - t) * (d + t)` THEN
  C1092MMNG10_PROD `&0 <= s * t` THEN
  SUBGOAL_THEN `s * t <= &1 / &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `s - t:real` REAL_LE_POW_2) THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    UNDISCH_TAC `&0 <= (c - s) * (c + s)` THEN
    UNDISCH_TAC `&0 <= (d - t) * (d + t)` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 / &2 - s * t) * c1092mncs_kC c s h r /\
                &0 <= (&43 / &500 - epsilon) * (s * t * c1092mncs_kC c s h r)`
    MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092mmncs_G10star] THEN
  UNDISCH_TAC `&47 / &1000 <= c1092mmncs_G10 c s d t h r` THEN
  UNDISCH_TAC `c1092mncs_kC c s h r <= &1` THEN
  REAL_ARITH_TAC);;
