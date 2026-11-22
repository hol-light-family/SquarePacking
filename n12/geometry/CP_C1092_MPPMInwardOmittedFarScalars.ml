(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardOmittedFarScalars.lean          *)
(* (namespace N12Compact.C1092MPPMInwardOmittedFar.Scalars).  Whole-interval *)
(* scalar comparisons for the omitted-G far ending.  Normal: c977cc_normal;  *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA; half_cross:   *)
(* C1092MIFE_HALF_CROSS; coordinates_after: C1092MIFSS_COORDINATES_AFTER;    *)
(* CanonicalProjection.after: CCCP_AFTER;                                    *)
(* C1092MPPMNonpositivePredecessor.norm_lt: C1092NPP_NORM_LT.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardOmittedFarBar.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessorScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalEndpoints.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessorScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;

let C1092IOFS_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: d0, t0, P, Q, a, sourceGap, targetGap, N (definitions) *)
let c1092iofs_d0 = new_definition `c1092iofs_d0 = &263000 / &319169`;;
let c1092iofs_t0 = new_definition `c1092iofs_t0 = &180831 / &319169`;;

let c1092iofs_P = new_definition
 `c1092iofs_P (d:real) (t:real) = &2 - d - t + (&11 / &25) * d * t`;;

let c1092iofs_Q = new_definition
 `c1092iofs_Q (d:real) (t:real) = d - t + &4 / &25 + (&11 / &25) * t pow 2`;;

let c1092iofs_a = new_definition
 `c1092iofs_a (c:real) (s:real) = &1 - c + (&2 / &5) * s`;;

let c1092iofs_sourceGap = new_definition
 `c1092iofs_sourceGap (c:real) (s:real) (d:real) (t:real) =
    c1092iofs_a c s + (c * d + s * t) * (&1 - d - t) +
    (c * t - s * d) * (&1 - t + (&14 / &25) * d)`;;

let c1092iofs_targetGap = new_definition
 `c1092iofs_targetGap (c:real) (s:real) (d:real) (t:real) =
    &1 - d - t + (c * d + s * t) * c1092iofs_a c s + (c * t - s * d) * (&108 / &125)`;;

let c1092iofs_N = new_definition
 `c1092iofs_N (x:real) =
    --(&100862498) * x pow 4 + &7307500 * x pow 3 + &70750700 * x pow 2 -
    &30508000 * x + &3946998`;;

(* Lean: endpoint *)
let C1092IOFS_ENDPOINT = prove
 (`c977cc_normal c1092iofs_d0 c1092iofs_t0`,
  REWRITE_TAC[c977cc_normal; c1092iofs_d0; c1092iofs_t0] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: source_bounds *)
let C1092IOFS_SOURCE_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &21 / &100
     ==> &91 / &100 < c /\ s < &41 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal (&9559 / &10441) (&4200 / &10441)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half (&9559 / &10441) (&4200 / &10441) = &21 / &100`
  ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&9559 / &10441`; `&4200 / &10441`]
    C1092MIFE_HALF_CROSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&9559 / &10441`; `&4200 / &10441`; `c:real`; `s:real`]
    C1092MIFSS_COORDINATES_AFTER) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: endpoint_order *)
let C1092IOFS_ENDPOINT_ORDER = prove
 (`forall d t. c977cc_normal d t /\ &237 / &763 <= C1092WPS_half d t
     ==> c1092iofs_t0 * d <= c1092iofs_d0 * t /\ d <= c1092iofs_d0 /\ c1092iofs_t0 <= t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `C1092WPS_half c1092iofs_d0 c1092iofs_t0 = &237 / &763` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half; c1092iofs_d0; c1092iofs_t0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`c1092iofs_d0`; `c1092iofs_t0`; `d:real`; `t:real`]
    C1092MIFE_HALF_CROSS) THEN
  ASM_REWRITE_TAC[C1092IOFS_ENDPOINT] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1092MIFSS_COORDINATES_AFTER THEN
  ASM_REWRITE_TAC[C1092IOFS_ENDPOINT]);;

(* Lean: coefficients_after (private) *)
let C1092IOFS_COEFFICIENTS_AFTER = prove
 (`forall d t. c977cc_normal d t /\ c1092iofs_t0 * d <= c1092iofs_d0 * t
     ==> c1092iofs_P d t <= c1092iofs_P c1092iofs_d0 c1092iofs_t0 /\
         c1092iofs_Q d t <= c1092iofs_Q c1092iofs_d0 c1092iofs_t0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c1092iofs_d0`; `c1092iofs_t0`]
    C1092MIFSS_COORDINATES_AFTER) THEN
  ASM_REWRITE_TAC[C1092IOFS_ENDPOINT] THEN STRIP_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  REWRITE_TAC[c1092iofs_P; c1092iofs_Q] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092iofs_d0; c1092iofs_t0]) THEN
  REWRITE_TAC[c1092iofs_d0; c1092iofs_t0] THEN
  ABBREV_TAC `D = d + &263000 / &319169` THEN
  ABBREV_TAC `TT = t + &180831 / &319169` THEN
  ABBREV_TAC `dc = &263000 / &319169 - d` THEN
  ABBREV_TAC `dt = t - &180831 / &319169` THEN
  SUBGOAL_THEN `&0 < D /\ &0 <= dc /\ &0 <= dt /\ &0 <= D - TT /\
                &0 <= &1 - (&11 / &50) * (D + TT) /\ TT <= &10 / &7` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "TT"; "dc"; "dt"] THEN C1092IOFS_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dc * D = dt * TT` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "TT"; "dc"; "dt"] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `D * ((&2 - d - t + (&11 / &25) * d * t) -
           (&2 - &263000 / &319169 - &180831 / &319169 +
            (&11 / &25) * &263000 / &319169 * &180831 / &319169)) =
      --(dt * (D - TT) * (&1 - (&11 / &50) * (D + TT)))` ASSUME_TAC THENL
     [UNDISCH_TAC `dc * D = dt * TT` THEN
      MAP_EVERY EXPAND_TAC ["D"; "TT"; "dc"; "dt"] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= dt * (D - TT) * (&1 - (&11 / &50) * (D + TT))` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 < D * ((&2 - d - t + (&11 / &25) * d * t) -
           (&2 - &263000 / &319169 - &180831 / &319169 +
            (&11 / &25) * &263000 / &319169 * &180831 / &319169))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    SUBGOAL_THEN `dt * (-- &1 + (&11 / &25) * TT) <= &0` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(d - t + &4 / &25 + (&11 / &25) * t pow 2) -
      (&263000 / &319169 - &180831 / &319169 + &4 / &25 +
       (&11 / &25) * (&180831 / &319169) pow 2) =
      --dc + dt * (-- &1 + (&11 / &25) * TT)` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["TT"; "dc"; "dt"] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]);;

(* Lean: source_positive *)
let C1092IOFS_SOURCE_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &237 / &763 <= C1092WPS_half d t
     ==> &0 < c1092iofs_sourceGap c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092IOFS_ENDPOINT_ORDER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092IOFS_COEFFICIENTS_AFTER) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c1092iofs_P; c1092iofs_Q; c1092iofs_d0; c1092iofs_t0] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  MP_TAC(SPECL [`&41 / &50`; `&14 / &25`; `c:real`; `s:real`; `&1`] C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN
   `c1092iofs_sourceGap c s d t =
    &1 - c * (&2 - d - t + (&11 / &25) * d * t) -
    s * (d - t + &4 / &25 + (&11 / &25) * t pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[c1092iofs_sourceGap; c1092iofs_a] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c * (&2 - d - t + (&11 / &25) * d * t) < c * (&41 / &50)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * (d - t + &4 / &25 + (&11 / &25) * t pow 2) <= s * (&14 / &25)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: polynomial_lower (private) *)
let C1092IOFS_POLYNOMIAL_LOWER = prove
 (`forall x. &0 <= x /\ x <= &21 / &100 ==> &500000 < c1092iofs_N x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c1092iofs_N] THEN
  SUBGOAL_THEN `&0 <= (&21 / &100 - x) * (&21 / &100 + x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= x pow 3 + x pow 2 * (&21 / &100) + x * (&21 / &100) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
    REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &30508000 - &70750700 * (x + &21 / &100) -
          &7307500 * (x pow 2 + x * (&21 / &100) + (&21 / &100) pow 2) +
          &100862498 * (x pow 3 + x pow 2 * (&21 / &100) + x * (&21 / &100) pow 2 +
                        (&21 / &100) pow 3)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&21 / &100 - x) *
          (&30508000 - &70750700 * (x + &21 / &100) -
          &7307500 * (x pow 2 + x * (&21 / &100) + (&21 / &100) pow 2) +
          &100862498 * (x pow 3 + x pow 2 * (&21 / &100) + x * (&21 / &100) pow 2 +
                        (&21 / &100) pow 3))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: target_endpoint (private) *)
let C1092IOFS_TARGET_ENDPOINT = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &21 / &100
     ==> &1 / &100 < c1092iofs_targetGap c s c1092iofs_d0 c1092iofs_t0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  MP_TAC(SPEC `x:real` C1092IOFS_POLYNOMIAL_LOWER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(&39896125 * (&1 + x pow 2) pow 2) * c1092iofs_targetGap c s c1092iofs_d0 c1092iofs_t0 =
    c1092iofs_N x` ASSUME_TAC THENL
   [REWRITE_TAC[c1092iofs_targetGap; c1092iofs_a; c1092iofs_N; c1092iofs_d0;
                c1092iofs_t0] THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &39896125 * (&1 + x pow 2) pow 2 /\
                &39896125 * (&1 + x pow 2) pow 2 < &50000000` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= &1 + x pow 2 /\ &1 + x pow 2 <= &21 / &20` MP_TAC THENL
     [UNDISCH_TAC `&0 <= x` THEN UNDISCH_TAC `x <= &21 / &100` THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
      MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
      CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`&1 + x pow 2`,`y:real`) THEN GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= y pow 2 /\ y pow 2 <= &441 / &400` MP_TAC THENL
     [CONJ_TAC THEN NLIN_TAC []; REAL_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(&39896125 * (&1 + x pow 2) pow 2) *
    c1092iofs_targetGap c s c1092iofs_d0 c1092iofs_t0 <=
    (&39896125 * (&1 + x pow 2) pow 2) * (&1 / &100)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: target_positive *)
let C1092IOFS_TARGET_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             C1092WPS_half c s <= &21 / &100 /\ &237 / &763 <= C1092WPS_half d t
     ==> &1 / &100 < c1092iofs_targetGap c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IOFS_TARGET_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IOFS_SOURCE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092IOFS_ENDPOINT_ORDER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `A = &1 + (&108 / &125) * s - c * c1092iofs_a c s` THEN
  ABBREV_TAC `B = &1 - (&108 / &125) * c - s * c1092iofs_a c s` THEN
  SUBGOAL_THEN `forall d t. c1092iofs_targetGap c s d t = &1 - A * d - B * t` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[c1092iofs_targetGap] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  MP_TAC C1092IOFS_ENDPOINT THEN DISCH_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= c1092iofs_a c s /\ c1092iofs_a c s < &13 / &50` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092iofs_a] THEN C1092IOFS_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * c1092iofs_a c s <= c1092iofs_a c s /\
                s * c1092iofs_a c s <= s * (&13 / &50) /\ &0 <= s * c1092iofs_a c s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN RASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN RASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&37 / &50 < A /\ B < &11 / &50 /\ &0 <= B` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN C1092IOFS_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c1092iofs_d0`; `c1092iofs_t0`; `A:real`; `B:real`]
    CCCP_AFTER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092iofs_d0; c1092iofs_t0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;
