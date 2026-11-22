(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointCoefficients.lean   *)
(* (N12Compact.C1092MPPMNegativeCrosspointSupport), NEGATIVE-WALL-SCALARS   *)
(* section 5.  Normal is c977cc_normal; P, Q, P2, Q2, FE, deltaE, E0 are     *)
(* c1092mncs_*; shallow_bounds C1092MNCC_SHALLOW_BOUNDS.  Lean d0, t0 keep   *)
(* their names; D, T are written out as d + d0, t + t0.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointCentral.ml";;

let C1092MNCF_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MNCF_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092MNCF_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092MNCF_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: second_order *)
let C1092MNCF_SECOND_ORDER = prove
 (`forall d t d0 t0. c977cc_normal d t /\ c977cc_normal d0 t0 /\ &8 * t <= &3 * d /\
               &8 * t0 <= &3 * d0 /\ t0 <= t
               ==> c1092mncs_P2 d t <= c1092mncs_P2 d0 t0 /\
                   c1092mncs_Q2 d t <= c1092mncs_Q2 d0 t0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MNCC_SHALLOW_BOUNDS) THEN
  MP_TAC(SPECL [`d0:real`; `t0:real`] C1092MNCC_SHALLOW_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092MNCC_NORMAL_TAC THEN
  C1092MNCF_PROD `&0 <= ((d + d0) - &93 / &50) * ((d + d0) + &93 / &50)` THEN
  C1092MNCF_PROD `&0 <= (&18 / &25 - (t + t0)) * (&18 / &25 + (t + t0))` THEN
  C1092MNCF_PROD `&0 <= (t + t0) * (&2 - (d + d0))` THEN
  SUBGOAL_THEN `(t + t0) * ((&61 / &100) * (d + d0) - &1) -
                (&13 / &40) * ((d + d0) pow 2 - (t + t0) pow 2) <= &0` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN C1092MNCF_LP_TAC; ALL_TAC] THEN
  C1092MNCF_PROD `&0 <= (&2 - (d + d0)) * (--(&1) + (&13 / &20) * (t + t0) + (&61 / &200) * (&2 + (d + d0)))` THEN
  C1092MNCF_PROD `&0 <= (&18 / &25 - (t + t0)) * (&13 / &10 - (&61 / &200) * (&18 / &25 + (t + t0)))` THEN
  SUBGOAL_THEN `--(d + d0) + (&13 / &20) * (d + d0) * (t + t0) +
                (&61 / &200) * ((d + d0) pow 2 - (t + t0) pow 2) <= &0` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN C1092MNCF_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(d + d0) * (c1092mncs_P2 d t - c1092mncs_P2 d0 t0) =
     (t - t0) * ((t + t0) * ((&61 / &100) * (d + d0) - &1) -
                 (&13 / &40) * ((d + d0) pow 2 - (t + t0) pow 2)) /\
     (d + d0) * (c1092mncs_Q2 d t - c1092mncs_Q2 d0 t0) =
     (t - t0) * (--(d + d0) + (&13 / &20) * (d + d0) * (t + t0) +
                 (&61 / &200) * ((d + d0) pow 2 - (t + t0) pow 2))` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092mncs_P2; c1092mncs_Q2] THEN CONJ_TAC THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `d0 pow 2 + t0 pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MNCF_PROD `&0 <= (t - t0) * --((t + t0) * ((&61 / &100) * (d + d0) - &1) -
                 (&13 / &40) * ((d + d0) pow 2 - (t + t0) pow 2))` THEN
  C1092MNCF_PROD `&0 <= (t - t0) * --(--(d + d0) + (&13 / &20) * (d + d0) * (t + t0) +
                 (&61 / &200) * ((d + d0) pow 2 - (t + t0) pow 2))` THEN
  CONJ_TAC THENL
  [MP_TAC(SPECL [`d + d0:real`; `c1092mncs_P2 d0 t0 - c1092mncs_P2 d t`] C1092MNCF_CANCEL);
   MP_TAC(SPECL [`d + d0:real`; `c1092mncs_Q2 d0 t0 - c1092mncs_Q2 d t`] C1092MNCF_CANCEL)] THEN
  ANTS_TAC THEN TRY REAL_ARITH_TAC THEN CONJ_TAC THEN C1092MNCF_LP_TAC);;

(* Lean: coefficient_bounds *)
let C1092MNCF_COEFFICIENT_BOUNDS = prove
 (`forall d t. c977cc_normal d t /\ &8 * t <= &3 * d
     ==> &0 <= c1092mncs_P d t /\ c1092mncs_P d t <= &3 / &10 /\
         &0 <= &1 - c1092mncs_Q d t /\ &1 - c1092mncs_Q d t <= &1 / &5 /\
         &1 - c1092mncs_Q d t <= c1092mncs_P d t /\ &1 / &3 < c1092mncs_P2 d t /\
         c1092mncs_P2 d t <= &13 / &20 /\ --(&1) - t <= c1092mncs_Q2 d t /\
         c1092mncs_Q2 d t <= --(&1) /\ &0 < &1 - (&61 / &100) * d - (&13 / &20) * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MNCC_SHALLOW_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MNCC_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&1`; `&0`] C1092MNCF_SECOND_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
                  RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092mncs_P; c1092mncs_Q; c1092mncs_P2; c1092mncs_Q2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092MNCF_PROD `&0 <= d * t` THEN C1092MNCF_PROD `&0 <= (&1 - d) * t` THEN
  C1092MNCF_PROD `&0 <= t * t` THEN
  C1092MNCF_PROD `&0 <= (&9 / &25 - t) * (&9 / &25 + t)` THEN
  C1092MNCF_PROD `&0 <= t * ((&37 / &50) * d - (&13 / &50) * t)` THEN
  C1092MNCF_PROD `&0 <= t * ((&12 / &25) * d - t)` THEN
  C1092MNCF_LP_TAC);;

(* Lean: support_join_identity *)
let C1092MNCF_SUPPORT_JOIN_IDENTITY = prove
 (`forall d t h r. c977cc_normal d t
     ==> (c1092mncs_P2 d t * h + c1092mncs_Q2 d t * r) -
         (--c1092mncs_P d t * h - c1092mncs_Q d t * r) =
         --c1092mncs_deltaE d t h r * (&1 - (&7 / &20) * d + (&9 / &100) * t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  REWRITE_TAC[c1092mncs_P2; c1092mncs_Q2; c1092mncs_P; c1092mncs_Q; c1092mncs_deltaE] THEN
  UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: FE_lower_formula *)
let C1092MNCF_FE_LOWER_FORMULA = prove
 (`forall d t h r. c977cc_normal d t /\ c1092mncs_deltaE d t h r <= &0
     ==> c1092mncs_FE d t h r = --c1092mncs_P d t * h - c1092mncs_Q d t * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= c1092mncs_deltaE d t h r` THEN ASM_REWRITE_TAC[c1092mncs_FE] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MNCF_SUPPORT_JOIN_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c1092mncs_deltaE d t h r = &0` SUBST1_TAC THENL
  [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: FE_upper_formula *)
let C1092MNCF_FE_UPPER_FORMULA = prove
 (`forall d t h r. &0 <= c1092mncs_deltaE d t h r
     ==> c1092mncs_FE d t h r = c1092mncs_P2 d t * h + c1092mncs_Q2 d t * r`,
  SIMP_TAC[c1092mncs_FE]);;

(* Lean: FE_aligned *)
let C1092MNCF_FE_ALIGNED = prove
 (`forall d t. c977cc_normal d t ==> c1092mncs_FE d t t d = c1092mncs_E0 d t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  REWRITE_TAC[c1092mncs_FE; c1092mncs_deltaE; REAL_ARITH `t * d - d * t = &0`; REAL_LE_REFL] THEN
  REWRITE_TAC[c1092mncs_P2; c1092mncs_Q2; c1092mncs_E0] THEN
  UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING);;
