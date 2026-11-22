(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryCoefficients.lean   *)
(* (N12Compact.C1092MPPMCrosspointSupport).  STEEP-POSITIVE-BOUNDARY-SCALARS *)
(* section 2: exact finite differences.  Normal: c977cc_normal; FE, kE,       *)
(* deltaE, E0: c1092mcs_*.  Real.sqrt is HOL's sqrt.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointSupportScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092MCBC_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MCBC_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MCBC_LIN_TAC; DISCH_TAC];;

let C1092MCBC_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MCBC_LIN_TAC; DISCH_TAC];;

let C1092MCBC_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

let C1092MCBC_NONNEG_OF_MUL = prove
 (`forall x y. &0 < x /\ &0 <= x * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:real`; `--y`] REAL_LT_MUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC);;

(* Lean: P *)
let c1092mcbc_P = new_definition
 `c1092mcbc_P (d:real) t = &1 - d - (&3 / &5) * t pow 2 + (&11 / &25) * d * t`;;

(* Lean: Q *)
let c1092mcbc_Q = new_definition
 `c1092mcbc_Q (d:real) t = &1 + t - (&11 / &25) * t pow 2 - (&3 / &5) * d * t`;;

(* Lean: FE_after *)
let C1092MCBC_FE_AFTER = prove
 (`forall d t h r. c977cc_normal d t /\ &0 <= c1092mcs_deltaE d t h r
     ==> c1092mcs_FE d t h r = c1092mcbc_P d t * h - c1092mcbc_Q d t * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[c1092mcs_FE] THEN
  REWRITE_TAC[c1092mcs_kE; c1092mcs_deltaE; c1092mcs_E0; c1092mcbc_P; c1092mcbc_Q] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  CONV_TAC REAL_RING);;

(* Lean: coefficient_order *)
let C1092MCBC_COEFFICIENT_ORDER = prove
 (`forall d t d0 t0. c977cc_normal d t /\ c977cc_normal d0 t0 /\ t0 <= t
     ==> c1092mcbc_P d0 t0 <= c1092mcbc_P d t /\ c1092mcbc_Q d0 t0 <= c1092mcbc_Q d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCBC_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  (* Thi *)
  C1092MCBC_LE_MUL_TAC `d - t` `d + t` THEN
  C1092MCBC_LE_MUL_TAC `d0 - t0` `d0 + t0` THEN
  SUBGOAL_THEN `t <= &5 / &7 /\ t0 <= &5 / &7` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `t - &5 / &7` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `t0 - &5 / &7` REAL_LE_SQUARE) THEN REPEAT DISCH_TAC THEN
    CONJ_TAC THEN C1092MCBC_LIN_TAC; ALL_TAC] THEN
  (* circle and difference *)
  MP_TAC(SPEC `d - d0` REAL_LE_SQUARE) THEN MP_TAC(SPEC `t - t0` REAL_LE_SQUARE) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(d + d0) * (d + d0) + (t + t0) * (t + t0) <= &4` ASSUME_TAC THENL
   [C1092MCBC_LIN_TAC; ALL_TAC] THEN
  C1092MCBC_LE_MUL_TAC `(d + d0) - (t + t0)` `(d + d0) + (t + t0)` THEN
  (* pbracket *)
  SUBGOAL_THEN
   `&0 <= (t + t0) * (&1 - (&3 / &5) * (d + d0)) +
          (&11 / &50) * ((d + d0) * (d + d0) - (t + t0) * (t + t0))` ASSUME_TAC THENL
   [ASM_CASES_TAC `d + d0 <= &5 / &3` THENL
     [C1092MCBC_LE_MUL_TAC `t + t0` `&1 - (&3 / &5) * (d + d0)` THEN C1092MCBC_LIN_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&5 / &3 <= d + d0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    C1092MCBC_LE_MUL_TAC `(d + d0) - &5 / &3` `(d + d0) + &5 / &3` THEN
    SUBGOAL_THEN `t + t0 <= &28 / &25` ASSUME_TAC THENL
     [MP_TAC(SPEC `(t + t0) - &28 / &25` REAL_LE_SQUARE) THEN DISCH_TAC THEN
      C1092MCBC_LIN_TAC; ALL_TAC] THEN
    C1092MCBC_LE_MUL_TAC `t + t0` `(&3 / &5) * (&2 - (d + d0))` THEN
    C1092MCBC_LE_MUL_TAC `t + t0` `&28 / &25 - (t + t0)` THEN
    C1092MCBC_LIN_TAC;
    ALL_TAC] THEN
  (* qbracket *)
  SUBGOAL_THEN
   `&0 <= (d + d0) * (&1 - (&11 / &25) * (t + t0)) - (&3 / &10) * (d + d0) * (d + d0) +
          (&3 / &10) * (t + t0) * (t + t0)` ASSUME_TAC THENL
   [C1092MCBC_LE_MUL_TAC `(d + d0) - &7 / &5` `&1 - (&11 / &25) * (t + t0)` THEN
    NLIN_TAC [SQ_NONNEG `(t + t0) - &77 / &150`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(d + d0) * (c1092mcbc_P d t - c1092mcbc_P d0 t0) =
    (t - t0) * ((t + t0) * (&1 - (&3 / &5) * (d + d0)) +
          (&11 / &50) * ((d + d0) * (d + d0) - (t + t0) * (t + t0))) /\
    (d + d0) * (c1092mcbc_Q d t - c1092mcbc_Q d0 t0) =
    (t - t0) * ((d + d0) * (&1 - (&11 / &25) * (t + t0)) -
          (&3 / &10) * (d + d0) * (d + d0) + (&3 / &10) * (t + t0) * (t + t0))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcbc_P; c1092mcbc_Q; REAL_POW_2] THEN
    UNDISCH_TAC `d * d + t * t = &1` THEN UNDISCH_TAC `d0 * d0 + t0 * t0 = &1` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN CONJ_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MCBC_LE_MUL_TAC `t - t0`
   `(t + t0) * (&1 - (&3 / &5) * (d + d0)) +
    (&11 / &50) * ((d + d0) * (d + d0) - (t + t0) * (t + t0))` THEN
  C1092MCBC_LE_MUL_TAC `t - t0`
   `(d + d0) * (&1 - (&11 / &25) * (t + t0)) - (&3 / &10) * (d + d0) * (d + d0) +
    (&3 / &10) * (t + t0) * (t + t0)` THEN
  SUBGOAL_THEN `&0 <= c1092mcbc_P d t - c1092mcbc_P d0 t0 /\ &0 <= c1092mcbc_Q d t - c1092mcbc_Q d0 t0` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC C1092MCBC_NONNEG_OF_MUL THEN EXISTS_TAC `d + d0` THEN
    CONJ_TAC THEN C1092MCBC_LIN_TAC;
    REAL_ARITH_TAC]);;

(* Lean: coefficient_bounds *)
let C1092MCBC_COEFFICIENT_BOUNDS = prove
 (`forall d t. c977cc_normal d t
     ==> &0 <= c1092mcbc_P d t /\ c1092mcbc_P d t < &213 / &1000 /\
         &1 <= c1092mcbc_Q d t /\ c1092mcbc_Q d t < &297 / &250 /\
         &203 / &250 < &2 - c1092mcbc_Q d t /\ &2 - c1092mcbc_Q d t <= &1 /\
         c1092mcbc_P d t + &2 - c1092mcbc_Q d t < &111 / &100`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `w = sqrt(&2) / &2` THEN
  SUBGOAL_THEN `&0 < w /\ w * w = &1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    MP_TAC(SPEC `&2` SQRT_POS_LT) THEN MP_TAC(SPEC `&2` SQRT_POW_2) THEN
    REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `(x / &2) * (x / &2) = (x * x) / &4`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&707 / &1000 < w /\ w < &177 / &250` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092MCBC_LE_MUL_TAC `&707 / &1000 - w` `&707 / &1000 + w` THEN C1092MCBC_LIN_TAC;
      MP_TAC(SPEC `w - &177 / &250` REAL_LE_SQUARE) THEN DISCH_TAC THEN C1092MCBC_LIN_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal w w /\ c977cc_normal (&1) (&0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MCBC_NORMAL_TAC THEN
  SUBGOAL_THEN `t <= w` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    C1092MCBC_LE_MUL_TAC `d - t` `d + t` THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MCBC_LT_MUL_TAC `t - w` `t + w` THEN C1092MCBC_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&1`; `&0`] C1092MCBC_COEFFICIENT_ORDER) THEN
  MP_TAC(SPECL [`w:real`; `w:real`; `d:real`; `t:real`] C1092MCBC_COEFFICIENT_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c1092mcbc_P; c1092mcbc_Q] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `d + t <= &283 / &200` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `d - t:real`; SQ_NONNEG `d + t - &283 / &200`]; ALL_TAC] THEN
  C1092MCBC_LE_MUL_TAC `&283 / &200 - (d + t)` `(&13 / &25) * (&283 / &200 + (d + t)) - &1` THEN
  MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN C1092MCBC_LIN_TAC);;

(* Lean: coefficient_difference *)
let C1092MCBC_COEFFICIENT_DIFFERENCE = prove
 (`forall d t. c977cc_normal d t ==> &89 / &100 <= c1092mcbc_Q d t - c1092mcbc_P d t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MCBC_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REWRITE_TAC[c1092mcbc_P; c1092mcbc_Q; REAL_POW_2] THEN
  SUBGOAL_THEN `d + t <= &283 / &200` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `d - t:real`; SQ_NONNEG `d + t - &283 / &200`]; ALL_TAC] THEN
  C1092MCBC_LE_MUL_TAC `d + t - &1` `&283 / &200 - (d + t)` THEN
  MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN C1092MCBC_LIN_TAC);;
