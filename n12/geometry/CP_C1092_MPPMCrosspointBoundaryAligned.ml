(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryAligned.lean        *)
(* (N12Compact.C1092MPPMCrosspointSupport), BOUNDARY-SCALARS section 3.     *)
(* Normal is c977cc_normal; FE, kE, deltaE, E0 are c1092mcs_*; P, Q,         *)
(* FE_after, coefficient_bounds c1092mcbc_ / C1092MCBC_*; diagonalValue,     *)
(* diagonal_lower c1092mcca_ / C1092MCCA_*; steep bounds C1092G10_*;         *)
(* sector bounds C977CSB_*; UnitCircleChord CCUCC_*; quarter_data            *)
(* C1092WPS_QUARTER_DATA.  Lean c0, s0, d0, t0 keep their names.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryCoefficients.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG10Clamp.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointCentralAligned.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

let C1092MCBA_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MCBA_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MCBA_LP_TAC; ALL_TAC];;

let C1092MCBA_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: alignedBoundary, alignedPoly (definitions) *)
let c1092mcba_alignedBoundary = new_definition
 `c1092mcba_alignedBoundary (c:real) (s:real) (d:real) (t:real) =
    &2 * c + s - &2 - (&543 / &500) * c * s - s * c1092mcs_FE d t c s`;;
let c1092mcba_alignedPoly = new_definition
 `c1092mcba_alignedPoly (c:real) (s:real) (d:real) (t:real) =
    &2 * c + s - &2 - (&543 / &500 + c1092mcbc_P d t) * c * s + c1092mcbc_Q d t * s pow 2`;;

(* Lean: aligned_form (private) *)
let C1092MCBA_ALIGNED_FORM = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ t <= s
     ==> c1092mcba_alignedBoundary c s d t = c1092mcba_alignedPoly c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] CCUCC_CROSS_ORDER) THEN
  ANTS_TAC THENL [C1092MCBC_NORMAL_TAC THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C1092MCBC_FE_AFTER) THEN
  ASM_REWRITE_TAC[c1092mcs_deltaE] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[c1092mcba_alignedBoundary; c1092mcba_alignedPoly] THEN REAL_ARITH_TAC);;

(* FE on the diagonal (the `support` step of aligned_self) *)
let C1092MCBA_FE_SELF = prove
 (`forall c s. c977cc_normal c s ==> c1092mcs_FE c s c s = c1092mcs_E0 c s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  REWRITE_TAC[c1092mcs_FE; c1092mcs_deltaE; c1092mcs_kE;
              REAL_ARITH `c * s - s * c = &0`; REAL_LE_REFL] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: aligned_self (private) *)
let C1092MCBA_ALIGNED_SELF = prove
 (`forall c s. c977cc_normal c s
     ==> c1092mcba_alignedBoundary c s c s = c1092mcca_diagonalValue c s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[c1092mcba_alignedBoundary; C1092MCBA_FE_SELF] THEN
  REWRITE_TAC[c1092mcs_E0; c1092mcca_diagonalValue] THEN REAL_ARITH_TAC);;

(* the bracket J of polynomial_order, in its sum/sum variables *)
let C1092MCBA_J_NONNEG = prove
 (`forall DD TT A Q. &0 < DD /\ &0 <= TT /\ TT <= DD /\ DD pow 2 + TT pow 2 <= &4 /\
             &14 / &5 <= DD + TT /\ A <= &1299 / &1000 /\ &1 <= Q
             ==> &0 <= DD - &2 * TT - (A / &2) * (DD pow 2 - TT pow 2) + Q * DD * TT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MCBA_PROD `&0 <= (DD - TT) * (DD + TT)` THEN
  C1092MCBA_PROD `&0 <= (DD pow 2 - TT pow 2) * (&1299 / &1000 - A)` THEN
  C1092MCBA_PROD `&0 <= (DD * TT) * (Q - &1)` THEN
  C1092MCBA_PROD `&0 <= (DD + TT - &14 / &5) * (&1 + TT)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  NLIN_TAC [SQ_NONNEG `TT - &100 / &299`]);;

(* Lean: polynomial_order (private) *)
let C1092MCBA_POLYNOMIAL_ORDER = prove
 (`forall c s c0 s0 d t. c977cc_normal c s /\ c977cc_normal c0 s0 /\ c977cc_normal d t /\
                   &3 / &5 <= s0 /\ s0 <= s
                   ==> c1092mcba_alignedPoly c0 s0 d t <= c1092mcba_alignedPoly c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&3 / &5 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`c0:real`; `s0:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MCBC_COEFFICIENT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092MCBC_NORMAL_TAC THEN
  MP_TAC(SPECL [`c + c0:real`; `s + s0:real`; `&543 / &500 + c1092mcbc_P d t`;
                `c1092mcbc_Q d t`] C1092MCBA_J_NONNEG) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN TRY C1092MCBA_LP_TAC THEN
   C1092MCBA_PROD `&0 <= (c - c0) * (c - c0)` THEN
   C1092MCBA_PROD `&0 <= (s - s0) * (s - s0)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
   C1092MCBA_LP_TAC; DISCH_TAC] THEN
  ABBREV_TAC `J = (c + c0) - &2 * (s + s0) -
                  ((&543 / &500 + c1092mcbc_P d t) / &2) * ((c + c0) pow 2 - (s + s0) pow 2) +
                  c1092mcbc_Q d t * (c + c0) * (s + s0)` THEN
  C1092MCBA_PROD `&0 <= (s - s0) * J` THEN
  SUBGOAL_THEN `(c + c0) * (c1092mcba_alignedPoly c s d t - c1092mcba_alignedPoly c0 s0 d t) =
                (s - s0) * J` ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN REWRITE_TAC[c1092mcba_alignedPoly] THEN
   UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `c0 pow 2 + s0 pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`c + c0:real`; `c1092mcba_alignedPoly c s d t - c1092mcba_alignedPoly c0 s0 d t`]
    C1092MCBA_CANCEL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MCBA_LP_TAC; REAL_ARITH_TAC]);;

(* the half-angle identity of low_endpoint *)
let C1092MCBA_LOW_IDENTITY = prove
 (`forall d t y. (&1 + y pow 2) * d = &1 - y pow 2 /\ (&1 + y pow 2) * t = &2 * y
     ==> &12500 * (&1 + y pow 2) pow 2 * c1092mcba_alignedPoly (&4 / &5) (&3 / &5) d t =
         &400 / &81 - (&3760 / &27) * (&1 / &3 - y) + (&22352 / &3) * (&1 / &3 - y) pow 2 -
         (&12976 / &3) * (&1 / &3 - y) pow 3 - &11516 * (&1 / &3 - y) pow 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + y pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d = (&1 - y pow 2) / (&1 + y pow 2) /\ t = (&2 * y) / (&1 + y pow 2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
  [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092mcba_alignedPoly; c1092mcbc_P; c1092mcbc_Q] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 < x ==> ~(x = &0)`)) THEN
  CONV_TAC REAL_FIELD);;

(* Lean: low_endpoint (private) *)
let C1092MCBA_LOW_ENDPOINT = prove
 (`forall d t. c977cc_normal d t /\ t <= &3 / &5
         ==> &0 < c1092mcba_alignedPoly (&4 / &5) (&3 / &5) d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `d:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
                  DISCH_TAC] THEN
  C1092MCBC_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half d t <= &1 / &3` MP_TAC THENL
  [REWRITE_TAC[C1092WPS_half] THEN
   SUBGOAL_THEN `&0 < &1 + d` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half d t`,`y:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `y:real`] C1092MCBA_LOW_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `z = &1 / &3 - y` THEN
  C1092MCBA_PROD `&0 <= (z * z) * (&1 / &3 - z)` THEN
  C1092MCBA_PROD `&0 <= (&1 / &3 - z) * (&1 / &3 + z)` THEN
  C1092MCBA_PROD `&0 <= (z * z) * (&1 / &9 - z * z)` THEN
  SUBGOAL_THEN `&0 < &400 / &81 - (&3760 / &27) * z + (&14188 / &3) * z pow 2` ASSUME_TAC THENL
  [SUBGOAL_THEN `&400 / &81 - (&3760 / &27) * z + (&14188 / &3) * z pow 2 =
                 (&14188 / &3) * (z - &470 / &31923) pow 2 + &3372800 / &861921` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPEC `z - &470 / &31923` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &12500 * (&1 + y pow 2) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN
    MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  C1092MCBA_PROD `&0 <= (&12500 * (&1 + y pow 2) pow 2) *
                         --c1092mcba_alignedPoly (&4 / &5) (&3 / &5) d t` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MCBA_LP_TAC);;

(* Lean: beforePoly (private definition) *)
let c1092mcba_beforePoly = new_definition
 `c1092mcba_beforePoly (c:real) (s:real) (d:real) (t:real) =
    c * (&1 - t pow 2 - (&3 / &50) * d * t - d) + s * (d * t - (&3 / &50) * t pow 2 - t - &1 / &2)`;;

(* Lean: before_form (private) *)
let C1092MCBA_BEFORE_FORM = prove
 (`forall c s d t. c977cc_normal d t /\ c1092mcs_deltaE d t c s <= &0
     ==> c1092mcs_FE d t c s = c1092mcba_beforePoly c s d t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= c1092mcs_deltaE d t c s` THEN
  ASM_REWRITE_TAC[c1092mcs_FE] THENL
  [SUBGOAL_THEN `c1092mcs_deltaE d t c s = &0` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[c1092mcs_kE; c1092mcs_E0; c1092mcba_beforePoly; c1092mcs_deltaE] THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
   REWRITE_TAC[c1092mcs_kE; c1092mcs_E0; c1092mcba_beforePoly; c1092mcs_deltaE] THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING]);;

(* Lean: before_order (private) *)
let C1092MCBA_BEFORE_ORDER = prove
 (`forall c s d t d0 t0. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal d0 t0 /\ t0 <= t
     ==> c1092mcba_beforePoly c s d t <= c1092mcba_beforePoly c s d0 t0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCBC_NORMAL_TAC THEN
  ABBREV_TAC `J = c * (t + t0) * (&1 - (d + d0)) -
                  (&3 / &100) * c * ((d + d0) pow 2 - (t + t0) pow 2) +
                  s * ((&1 / &2) * ((d + d0) pow 2 - (t + t0) pow 2) -
                       (&3 / &50) * (d + d0) * (t + t0) - (d + d0))` THEN
  C1092MCBA_PROD `&0 <= ((d + d0) - (t + t0)) * ((d + d0) + (t + t0))` THEN
  C1092MCBA_PROD `&0 <= (c * (t + t0)) * ((d + d0) - &1)` THEN
  C1092MCBA_PROD `&0 <= c * (((d + d0) - (t + t0)) * ((d + d0) + (t + t0)))` THEN
  C1092MCBA_PROD `&0 <= (d + d0) * (&1 - (d + d0) / &2)` THEN
  C1092MCBA_PROD `&0 <= (d + d0) * (t + t0)` THEN
  C1092MCBA_PROD `&0 <= (t + t0) * (t + t0)` THEN
  SUBGOAL_THEN `(&1 / &2) * ((d + d0) pow 2 - (t + t0) pow 2) -
                (&3 / &50) * (d + d0) * (t + t0) - (d + d0) <= &0` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN C1092MCBA_LP_TAC; ALL_TAC] THEN
  C1092MCBA_PROD `&0 <= s * --((&1 / &2) * ((d + d0) pow 2 - (t + t0) pow 2) -
                (&3 / &50) * (d + d0) * (t + t0) - (d + d0))` THEN
  SUBGOAL_THEN `J <= &0` ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN REWRITE_TAC[REAL_POW_2] THEN C1092MCBA_LP_TAC; ALL_TAC] THEN
  C1092MCBA_PROD `&0 <= (t - t0) * --J` THEN
  SUBGOAL_THEN `(d + d0) * (c1092mcba_beforePoly c s d t - c1092mcba_beforePoly c s d0 t0) =
                (t - t0) * J` ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN REWRITE_TAC[c1092mcba_beforePoly] THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `d0 pow 2 + t0 pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`d + d0:real`; `c1092mcba_beforePoly c s d0 t0 - c1092mcba_beforePoly c s d t`]
    C1092MCBA_CANCEL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MCBA_LP_TAC; REAL_ARITH_TAC]);;

let C1092MCBA_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c1092mcs_deltaE] THEN REPEAT CONJ_TAC THEN
                  FIRST [RASM_ARITH_TAC; REWRITE_TAC[c977cc_normal] THEN
                         CONV_TAC REAL_RAT_REDUCE_CONV]; DISCH_TAC];;

(* Lean: FE_before_aligned_cap *)
let C1092MCBA_FE_BEFORE_ALIGNED_CAP = prove
 (`forall h r d t. c977cc_normal h r /\ c977cc_normal d t /\ r <= t
     ==> c1092mcs_FE d t h r <= c1092mcs_E0 h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `d:real`; `t:real`] CCUCC_CROSS_ORDER) THEN
  ANTS_TAC THENL [C1092MCBC_NORMAL_TAC THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  C1092MCBA_USE C1092MCBA_BEFORE_FORM [`h:real`; `r:real`; `d:real`; `t:real`] THEN
  C1092MCBA_USE C1092MCBA_BEFORE_FORM [`h:real`; `r:real`; `h:real`; `r:real`] THEN
  C1092MCBA_USE C1092MCBA_BEFORE_ORDER [`h:real`; `r:real`; `d:real`; `t:real`; `h:real`; `r:real`] THEN
  C1092MCBA_USE C1092MCBA_FE_SELF [`h:real`; `r:real`] THEN
  RASM_ARITH_TAC);;

(* Lean: alignedBoundary_positive *)
let C1092MCBA_ALIGNEDBOUNDARY_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s
     ==> &0 < c1092mcba_alignedBoundary c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t <= s` THENL
  [C1092MCBA_USE C1092MCBA_ALIGNED_FORM [`c:real`; `s:real`; `d:real`; `t:real`] THEN
   ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `t <= &3 / &5` THENL
   [C1092MCBA_USE C1092MCBA_POLYNOMIAL_ORDER
      [`c:real`; `s:real`; `&4 / &5`; `&3 / &5`; `d:real`; `t:real`] THEN
    C1092MCBA_USE C1092MCBA_LOW_ENDPOINT [`d:real`; `t:real`] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `&3 / &5 <= t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    C1092MCBA_USE C1092MCBA_POLYNOMIAL_ORDER
      [`c:real`; `s:real`; `d:real`; `t:real`; `d:real`; `t:real`] THEN
    C1092MCBA_USE C1092MCCA_DIAGONAL_LOWER [`d:real`; `t:real`] THEN
    C1092MCBA_USE C1092MCBA_ALIGNED_SELF [`d:real`; `t:real`] THEN
    C1092MCBA_USE C1092MCBA_ALIGNED_FORM [`d:real`; `t:real`; `d:real`; `t:real`] THEN
    RASM_ARITH_TAC];
   SUBGOAL_THEN `s <= t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CCUCC_CROSS_ORDER) THEN
   ANTS_TAC THENL [C1092MCBC_NORMAL_TAC THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   C1092MCBA_USE C1092MCBA_BEFORE_FORM [`c:real`; `s:real`; `d:real`; `t:real`] THEN
   C1092MCBA_USE C1092MCBA_BEFORE_FORM [`c:real`; `s:real`; `c:real`; `s:real`] THEN
   C1092MCBA_USE C1092MCBA_BEFORE_ORDER [`c:real`; `s:real`; `d:real`; `t:real`; `c:real`; `s:real`] THEN
   C1092MCBA_USE C1092MCBA_ALIGNED_SELF [`c:real`; `s:real`] THEN
   C1092MCBA_USE C1092MCCA_DIAGONAL_LOWER [`c:real`; `s:real`] THEN
   C1092MCBC_NORMAL_TAC THEN
   C1092MCBA_PROD `&0 <= s * (c1092mcs_FE c s c s - c1092mcs_FE d t c s)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[c1092mcba_alignedBoundary]) THEN
   REWRITE_TAC[c1092mcba_alignedBoundary] THEN
   RASM_ARITH_TAC]);;
