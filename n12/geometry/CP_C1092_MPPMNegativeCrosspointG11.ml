(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointG11.lean           *)
(* (N12Compact.C1092MPPMNegativeCrosspointSupport), NEGATIVE-WALL-SCALARS    *)
(* section 6 on the domain h <= r.  Normal: c977cc_normal; Quarter, G10,     *)
(* G11, FC, FE, P, Q, P2, Q2, kE, deltaE, E0: c1092mncs_*;                   *)
(* sine_order / cosine_order: C977CSB_*; FC_high_cap: C1092NCCL_FC_HIGH_CAP; *)
(* G10_nonnegative: C1092NG10H_G10_NONNEGATIVE; second_order, FE formulas:   *)
(* C1092MNCF_*; UnitCircleChord: CCUCC_*.  Lean D, T renamed DD, TT.         *)
(* Tag C1092NG11_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointCoefficients.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointG10High.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092NG11_LIN = REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092NG11_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
   (MATCH_ACCEPT_TAC REAL_LE_POW_2 ORELSE C1092NG11_LIN); ALL_TAC];;

let C1092NG11_UNFOLD_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC));;

let C1092NG11_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092NG11_QUARTER_NORMAL = prove
 (`forall h r. c1092mncs_quarter h r /\ h <= r ==> c977cc_normal r h`,
  REWRITE_TAC[c977cc_normal; c1092mncs_quarter; c1092mcs_quarter] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: radial (private) *)
let C1092NG11_RADIAL = prove
 (`forall h r. c1092mncs_quarter h r /\ h <= r
     ==> &0 < r /\ &0 <= h / r /\ h / r <= &1 /\ h = (h / r) * r /\
         (&1 + (h / r) pow 2) * r pow 2 = &1 /\
         r pow 2 * (&1 + h / r) * (&1 + (&2 / &5) * (h / r) pow 2) <= h + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NG11_UNFOLD_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `r = &0 /\ h = &0` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `h = (h / r) * r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ABBREV_TAC `u = h / r` THEN
  SUBGOAL_THEN `&0 <= u /\ u <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
     [SUBGOAL_THEN `&0 < (--u) * r` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < (u - &1) * r` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + u pow 2) * r pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN UNDISCH_TAC `h = u * r` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r * (&1 + (&2 / &5) * u pow 2) <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= r pow 2 * u pow 2 * (&1 / &5 - (&4 / &25) * u pow 2)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      SUBGOAL_THEN `u pow 2 <= &1` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN
        MP_TAC(SPECL [`u:real`; `&1`; `u:real`; `&1`] REAL_LE_MUL2) THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 - (r * (&1 + (&2 / &5) * u pow 2)) pow 2 =
                  r pow 2 * u pow 2 * (&1 / &5 - (&4 / &25) * u pow 2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(&1 + u pow 2) * r pow 2 = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (r * (&1 + (&2 / &5) * u pow 2) - &1) *
                       (r * (&1 + (&2 / &5) * u pow 2) + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&1 - (r * (&1 + (&2 / &5) * u pow 2)) pow 2 =
                 r pow 2 * u pow 2 * (&1 / &5 - (&4 / &25) * u pow 2)` THEN
    UNDISCH_TAC `&0 <= r pow 2 * u pow 2 * (&1 / &5 - (&4 / &25) * u pow 2)` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r * (&1 + u)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`r * (&1 + u)`; `r * (&1 + (&2 / &5) * u pow 2)`; `&1`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: zero_model (private) *)
let C1092NG11_ZERO_MODEL = prove
 (`forall c s h r. c977cc_normal c s /\ c1092mncs_quarter h r /\ h <= r
     ==> &0 <= h + r - &2 - h * c1092mncs_FC c s h r + r pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092NG11_RADIAL) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_HIGH_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `u = h / r` THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C1092NG11_UNFOLD_TAC THEN
  C1092NG11_PROD `&0 <= h * ((--h / &2 + (&9 / &100) * r) - c1092mncs_FC c s h r)` THEN
  C1092NG11_PROD `&0 <= (&1 - u) * (&11 / &10 - (&2 / &5) * (&1 + u))` THEN
  SUBGOAL_THEN `&0 <= &91 / &100 - (&11 / &10) * u + (&2 / &5) * u pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN C1092NG11_LIN; ALL_TAC] THEN
  C1092NG11_PROD `&0 <= r pow 2 * u * (&91 / &100 - (&11 / &10) * u + (&2 / &5) * u pow 2)` THEN
  SUBGOAL_THEN `h + r - &2 + h pow 2 / &2 - (&9 / &100) * h * r + r pow 2 =
      r pow 2 * u * (&91 / &100 - (&11 / &10) * u + (&2 / &5) * u pow 2) +
      (h + r - r pow 2 * (&1 + u) * (&1 + (&2 / &5) * u pow 2))` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + u pow 2) * r pow 2 = &1` THEN
    FIRST_X_ASSUM(fun th -> if concl th = `h = u * r` then SUBST1_TAC th else NO_TAC) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  C1092NG11_LIN);;

(* Lean: slope_model (private) *)
let C1092NG11_SLOPE_MODEL = prove
 (`forall c s h r. c977cc_normal c s /\ c1092mncs_quarter h r /\ h <= r /\ &3 * r <= &8 * h
     ==> &0 <= h + r - &2 - h * c1092mncs_FC c s h r + (&771 / &3650) * h * r +
               (&601 / &730) * r pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092NG11_RADIAL) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_HIGH_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `u = h / r` THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C1092NG11_UNFOLD_TAC THEN
  SUBGOAL_THEN `&3 / &8 <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (&3 / &8 - u) * r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 / &5) * u pow 2 - (&19 / &20) * u + &611 / &800` ASSUME_TAC THENL
   [MP_TAC(SPEC `u - &19 / &16` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092NG11_PROD `&0 <= (u - &3 / &8) *
     ((&2 / &5) * u pow 2 - (&19 / &20) * u + &611 / &800)` THEN
  SUBGOAL_THEN `&0 <= -- &9 / &50 + (&28 / &25) * u - (&11 / &10) * u pow 2 +
                       (&2 / &5) * u pow 3` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= (u - &3 / &8) *
       ((&2 / &5) * u pow 2 - (&19 / &20) * u + &611 / &800)` THEN
    REWRITE_TAC[REAL_ARITH `u pow 3 = u * u * u`; REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092NG11_PROD `&0 <= r pow 2 * (-- &9 / &50 + (&28 / &25) * u - (&11 / &10) * u pow 2 +
                                   (&2 / &5) * u pow 3)` THEN
  C1092NG11_PROD `&0 <= h * ((--h / &2 + (&9 / &100) * r) - c1092mncs_FC c s h r)` THEN
  SUBGOAL_THEN `h + r - &2 + h pow 2 / &2 + (&3 / &25) * h * r + (&41 / &50) * r pow 2 =
      r pow 2 * (-- &9 / &50 + (&28 / &25) * u - (&11 / &10) * u pow 2 + (&2 / &5) * u pow 3) +
      (h + r - r pow 2 * (&1 + u) * (&1 + (&2 / &5) * u pow 2))` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + u pow 2) * r pow 2 = &1` THEN
    FIRST_X_ASSUM(fun th -> if concl th = `h = u * r` then SUBST1_TAC th else NO_TAC) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  C1092NG11_PROD `&0 <= h * r` THEN
  MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  C1092NG11_LIN);;

(* Lean: doubleC / doubleS (private definitions) *)
let c1092ng11_doubleC = new_definition
 `c1092ng11_doubleC (d:real) (t:real) = d pow 2 - t pow 2`;;
let c1092ng11_doubleS = new_definition
 `c1092ng11_doubleS (d:real) (t:real) = &2 * d * t`;;

(* Lean: double_quarter (private) *)
let C1092NG11_DOUBLE_QUARTER = prove
 (`forall d t. c977cc_normal d t
         ==> c1092mncs_quarter (c1092ng11_doubleC d t) (c1092ng11_doubleS d t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  C1092NG11_NORMAL_TAC THEN
  REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter; c1092ng11_doubleC; c1092ng11_doubleS] THEN
  REPEAT CONJ_TAC THENL
   [C1092NG11_PROD `&0 <= (d - t) * (d + t)` THEN
    REWRITE_TAC[REAL_POW_2] THEN C1092NG11_LIN;
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING]);;

(* Lean: double_order (private) *)
let C1092NG11_DOUBLE_ORDER = prove
 (`forall d t DD TT. c977cc_normal d t /\ c977cc_normal DD TT /\ t <= TT
               ==> c1092ng11_doubleS d t <= c1092ng11_doubleS DD TT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092NG11_DOUBLE_QUARTER) THEN
  MP_TAC(SPECL [`DD:real`; `TT:real`] C1092NG11_DOUBLE_QUARTER) THEN
  ASM_REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CCUCC_COSINE_ORDER THEN
  MAP_EVERY EXISTS_TAC [`c1092ng11_doubleC DD TT`; `c1092ng11_doubleC d t`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC) THEN
  C1092NG11_NORMAL_TAC THEN
  C1092NG11_PROD `&0 <= (TT - t) * (t + TT)` THEN
  REWRITE_TAC[c1092ng11_doubleC] THEN
  UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `DD pow 2 + TT pow 2 = &1` THEN
  UNDISCH_TAC `&0 <= (TT - t) * (t + TT)` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: A / B / base (private definitions) *)
let c1092ng11_A = new_definition
 `c1092ng11_A (h:real) (r:real) = (&13 / &100) * h * r + (&37 / &100) * r pow 2`;;
let c1092ng11_B = new_definition
 `c1092ng11_B (h:real) (r:real) = (&37 / &100) * h * r - (&13 / &100) * r pow 2`;;
let c1092ng11_base = new_definition
 `c1092ng11_base (c:real) (s:real) (h:real) (r:real) =
    h + r - &2 - h * c1092mncs_FC c s h r + r pow 2 - c1092ng11_A h r`;;

(* Lean: before_form (private) *)
let C1092NG11_BEFORE_FORM = prove
 (`forall c s d t h r. c977cc_normal d t /\ c1092mncs_deltaE d t h r <= &0
     ==> c1092mncs_G11 c s d t h r =
         c1092ng11_base c s h r + c1092ng11_A h r * c1092ng11_doubleC d t +
         c1092ng11_B h r * c1092ng11_doubleS d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[c1092mncs_G11; C1092MNCF_FE_LOWER_FORMULA] THEN
  C1092NG11_NORMAL_TAC THEN
  REWRITE_TAC[c1092ng11_base; c1092ng11_A; c1092ng11_B; c1092ng11_doubleC;
              c1092ng11_doubleS; c1092mncs_P; c1092mncs_Q] THEN
  UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: aligned (private) *)
let C1092NG11_ALIGNED = prove
 (`forall c s h r. c1092mncs_quarter h r /\ c977cc_normal r h
     ==> c1092mncs_G11 c s r h h r = c1092mncs_G10 c s r h h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[c1092mncs_G11; c1092mncs_G10; C1092MNCF_FE_ALIGNED] THEN
  REWRITE_TAC[c1092mncs_deltaE; c1092mncs_kE; REAL_ARITH `h * r - r * h = &0`;
              REAL_ABS_0] THEN
  C1092NG11_UNFOLD_TAC THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: before (private) *)
let C1092NG11_BEFORE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &8 * t <= &3 * d /\ c1092mncs_quarter h r /\ h <= r /\
     c1092mncs_deltaE d t h r <= &0
     ==> &0 <= c1092mncs_G11 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092NG11_QUARTER_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092NG11_DOUBLE_QUARTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= c1092ng11_A h r` ASSUME_TAC THENL
   [REWRITE_TAC[c1092ng11_A] THEN C1092NG11_UNFOLD_TAC THEN
    C1092NG11_PROD `&0 <= h * r` THEN MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092ng11_base c s h r + c1092ng11_A h r * &1 +
                     c1092ng11_B h r * &0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NG11_ZERO_MODEL) THEN
    ASM_REWRITE_TAC[c1092ng11_base] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[C1092NG11_BEFORE_FORM] THEN
  ASM_CASES_TAC `&8 * h <= &3 * r` THENL
   [MP_TAC(SPECL [`r:real`; `h:real`; `d:real`; `t:real`] C977CSB_SINE_ORDER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c1092mncs_deltaE d t h r <= &0` THEN
      REWRITE_TAC[c1092mncs_deltaE] THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(SPECL [`r:real`; `h:real`] C1092NG11_DOUBLE_QUARTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `h:real`; `h:real`; `r:real`]
      C1092NG10H_G10_NONNEGATIVE) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM C1092NG11_ALIGNED] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `h:real`; `h:real`; `r:real`]
      C1092NG11_BEFORE_FORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c1092mncs_deltaE] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN DISCH_TAC] THEN
    MP_TAC(SPECL [`d:real`; `t:real`; `r:real`; `h:real`] C1092NG11_DOUBLE_ORDER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC CCUCC_LINEAR_NONNEGATIVE THEN
    MAP_EVERY EXISTS_TAC [`&1`; `&0`; `c1092ng11_doubleC r h`; `c1092ng11_doubleS r h`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `c1092ng11_doubleS d t <= &48 / &73` ASSUME_TAC THENL
   [C1092NG11_NORMAL_TAC THEN
    FIRST_ASSUM(fun th -> if concl th = `c977cc_normal d t`
      then STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) else NO_TAC) THEN
    C1092NG11_PROD `&0 <= (&3 * d - &8 * t) * (&8 * d - &3 * t)` THEN
    REWRITE_TAC[c1092ng11_doubleS] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
    UNDISCH_TAC `&0 <= (&3 * d - &8 * t) * (&8 * d - &3 * t)` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092ng11_base c s h r + c1092ng11_A h r * (&55 / &73) +
                     c1092ng11_B h r * (&48 / &73)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NG11_SLOPE_MODEL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[c1092ng11_base; c1092ng11_A; c1092ng11_B] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CCUCC_LINEAR_NONNEGATIVE THEN
  MAP_EVERY EXISTS_TAC [`&1`; `&0`; `&55 / &73`; `&48 / &73`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: after (private) *)
let C1092NG11_AFTER = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &8 * t <= &3 * d /\ c1092mncs_quarter h r /\ h <= r /\
     &0 <= c1092mncs_deltaE d t h r
     ==> &0 <= c1092mncs_G11 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092NG11_QUARTER_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `r:real`; `h:real`] C977CSB_SINE_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= c1092mncs_deltaE d t h r` THEN
    REWRITE_TAC[c1092mncs_deltaE] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `r:real`; `h:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&8 * h <= &3 * r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `r:real`; `h:real`] C1092MNCF_SECOND_ORDER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1092mncs_FE d t h r <= c1092mncs_FE r h h r` ASSUME_TAC THENL
   [MP_TAC(SPECL [`r:real`; `h:real`; `h:real`; `r:real`] C1092MNCF_FE_UPPER_FORMULA) THEN
    MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MNCF_FE_UPPER_FORMULA) THEN
    ASM_REWRITE_TAC[c1092mncs_deltaE; REAL_ARITH `h * r - r * h = &0`; REAL_LE_REFL] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN C1092NG11_UNFOLD_TAC THEN
    C1092NG11_PROD `&0 <= (c1092mncs_P2 r h - c1092mncs_P2 d t) * h` THEN
    C1092NG11_PROD `&0 <= (c1092mncs_Q2 r h - c1092mncs_Q2 d t) * r` THEN
    C1092NG11_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `h:real`; `h:real`; `r:real`]
    C1092NG10H_G10_NONNEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM C1092NG11_ALIGNED] THEN
  REWRITE_TAC[c1092mncs_G11] THEN DISCH_TAC THEN C1092NG11_UNFOLD_TAC THEN
  C1092NG11_PROD `&0 <= r * (c1092mncs_FE r h h r - c1092mncs_FE d t h r)` THEN
  C1092NG11_LIN);;

(* Lean: G11_nonnegative *)
let C1092NG11_G11_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &8 * t <= &3 * d /\ c1092mncs_quarter h r /\ h <= r
     ==> &0 <= c1092mncs_G11 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= c1092mncs_deltaE d t h r` THENL
   [MATCH_MP_TAC C1092NG11_AFTER; MATCH_MP_TAC C1092NG11_BEFORE] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
