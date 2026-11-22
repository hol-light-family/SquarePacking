(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOnePositiveScalars.lean               *)
(* (N12Compact.C1092MPPMOnePositive).  ONE-POSITIVE-CONTINUOUS-ENDING Lemma *)
(* 2, longitudinal scalar (the Lean header says "Source only, uncompiled"). *)
(* Normal is c977cc_normal; half / normal_half / rho_bounds C1092MCBH_*     *)
(* (rho = c1092mpba_diagonal); QuadraticArc remainder / X / Y / Z / sum3 /  *)
(* pair3 / triple3 / value / nonnegative c1092mpqa_* / C1092MPQA_*;         *)
(* NonpositivePredecessor.norm_le C1092NPP_NORM_LE; large_sum               *)
(* C1092MMNCE_LARGE_SUM; cosine_order C977CSB_COSINE_ORDER; the value at    *)
(* rho C1092MNCG11_RHO_VALUE.  Tag C1092OPS_ / c1092ops_.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointG11.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessorScalars.ml";;

let C1092OPS_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092OPS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092OPS_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092OPS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: positiveP, positiveQ (definitions) *)
let c1092ops_positiveP = new_definition
 `c1092ops_positiveP (d:real) (t:real) = &2 - d - t + (&11 / &25) * d * t`;;
let c1092ops_positiveQ = new_definition
 `c1092ops_positiveQ (d:real) (t:real) = &1 - d + t - (&11 / &25) * t pow 2`;;

(* Lean: positive_remainder (private) *)
let C1092OPS_POSITIVE_REMAINDER = prove
 (`forall c s q z r. c977cc_normal c s /\ &97 / &100 <= c /\
     &0 <= q /\ q <= &5 / &12 /\ &0 <= z /\ z <= &5 / &12 /\ &0 <= r /\ r <= &5 / &12
     ==> &0 <= c1092mpqa_remainder (--(&11 / &25) * s) (--(&11 / &25) * c)
                                   (&99 / &100 - &2 * c - (&14 / &25) * s) q z r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092OPS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= c1092mpqa_sum3 q z r /\ &0 <= c1092mpqa_pair3 q z r /\
                &0 <= c1092mpqa_triple3 q z r /\
                c1092mpqa_triple3 q z r <= c1092mpqa_sum3 q z r` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092mpqa_sum3; c1092mpqa_pair3; c1092mpqa_triple3] THEN
   C1092OPS_PROD `&0 <= q * z` THEN C1092OPS_PROD `&0 <= q * r` THEN
   C1092OPS_PROD `&0 <= z * r` THEN C1092OPS_PROD `&0 <= z * (&5 / &12 - r)` THEN
   C1092OPS_PROD `&0 <= q * (&1 - z * r)` THEN C1092OPS_PROD `&0 <= q * z * r` THEN
   C1092OPS_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092mpqa_X q z r <= &1 /\ c1092mpqa_Y q z r <= c1092mpqa_sum3 q z r`
    STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092mpqa_X; c1092mpqa_Y] THEN
   C1092OPS_PROD `&0 <= (c1092mpqa_sum3 q z r - c1092mpqa_triple3 q z r) *
                        (c1092mpqa_sum3 q z r + c1092mpqa_triple3 q z r)` THEN
   C1092OPS_PROD `&0 <= c1092mpqa_pair3 q z r * c1092mpqa_pair3 q z r` THEN
   C1092OPS_PROD `&0 <= c1092mpqa_triple3 q z r * c1092mpqa_pair3 q z r` THEN
   REWRITE_TAC[REAL_POW_2] THEN C1092OPS_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + (c1092mpqa_sum3 q z r) pow 2 / &3 <= c1092mpqa_Z q z r` ASSUME_TAC THENL
  [SUBGOAL_THEN
    `&3 * (c1092mpqa_Z q z r - &1) - (c1092mpqa_sum3 q z r) pow 2 =
     (q - z) pow 2 + (q - r) pow 2 + (z - r) pow 2 +
     &3 * ((q * z) pow 2 + (q * r) pow 2 + (z * r) pow 2 + (q * z * r) pow 2)` MP_TAC THENL
   [REWRITE_TAC[c1092mpqa_Z; c1092mpqa_sum3] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN
    `&0 <= (q - z) pow 2 + (q - r) pow 2 + (z - r) pow 2 +
          &3 * ((q * z) pow 2 + (q * r) pow 2 + (z * r) pow 2 + (q * z * r) pow 2)`
     MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c1092mpqa_sum3 q z r) pow 2 /\
                &0 <= (c1092mpqa_sum3 q z r - &66 / &47) pow 2` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c1092mpqa_Z q z r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092OPS_PROD `&0 <= (&2 * c - &99 / &100) *
                       (c1092mpqa_Z q z r - &1 - (c1092mpqa_sum3 q z r) pow 2 / &3)` THEN
  C1092OPS_PROD `&0 <= (&2 * c - &99 / &100 - &47 / &50) *
                       (&1 + (c1092mpqa_sum3 q z r) pow 2 / &3)` THEN
  C1092OPS_PROD `&0 <= c * (c1092mpqa_sum3 q z r - c1092mpqa_Y q z r)` THEN
  C1092OPS_PROD `&0 <= (&1 - c) * c1092mpqa_sum3 q z r` THEN
  C1092OPS_PROD `&0 <= s * (c1092mpqa_Z q z r - &1)` THEN
  C1092OPS_PROD `&0 <= s * (&1 - c1092mpqa_X q z r)` THEN
  REWRITE_TAC[c1092mpqa_remainder] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092OPS_LP_TAC);;

(* Lean: positive_longitudinal *)
let C1092OPS_POSITIVE_LONGITUDINAL = prove
 (`forall c s d t. c977cc_normal c s /\ &97 / &100 <= c /\ &4 * s <= c /\ c977cc_normal d t /\
             &13 / &87 <= c1092mcbh_half d t
     ==> &1 / &100 <= &1 - c1092ops_positiveP d t * c - c1092ops_positiveQ d t * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MCBH_NORMAL_HALF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC C1092MCBH_RHO_BOUNDS THEN
  C1092OPS_NORMAL_TAC THEN
  MP_TAC(SPECL [`&9 / &10`; `&2 / &5`; `c:real`; `s:real`; `&99 / &100`] C1092NPP_NORM_LE) THEN
  MP_TAC(SPECL [`&91 / &100`; `&19 / &50`; `c:real`; `s:real`; `&99 / &100`] C1092NPP_NORM_LE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &87`; `c1092mcbh_half d t`; `c1092mpba_diagonal`]
    C1092OPS_POSITIVE_REMAINDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC C1092MNCG11_SQRT_LOWER THEN
  MP_TAC C1092MNCG11_DIAGONAL_NORMAL THEN REWRITE_TAC[c977cc_normal] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&707 / &1000 <= sqrt(&2) / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092OPS_PROD `&0 < (&707 / &1000 - sqrt(&2) / &2) * (&707 / &1000 + sqrt(&2) / &2)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092OPS_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`--(&11 / &25) * s`; `--(&11 / &25) * c`; `&99 / &100 - &2 * c - (&14 / &25) * s`;
                `c + s`; `c - s`; `&13 / &87`; `c1092mcbh_half d t`; `c1092mpba_diagonal`]
               C1092MPQA_NONNEGATIVE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[C1092MNCG11_RHO_VALUE] THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    REWRITE_TAC[c1092mpqa_value; c1092sps_cosH; c1092sps_sinH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN C1092OPS_LP_TAC;
    C1092OPS_PROD `&0 <= c * (sqrt(&2) / &2 - &707 / &1000)` THEN C1092OPS_LP_TAC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092mpqa_value] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `--(&11 / &25) * s * d pow 2 + (--(&11 / &25) * c) * d * t +
    (&99 / &100 - &2 * c - (&14 / &25) * s) + (c + s) * d + (c - s) * t =
    &1 - c1092ops_positiveP d t * c - c1092ops_positiveQ d t * s - &1 / &100`
    ASSUME_TAC THENL
  [REWRITE_TAC[c1092ops_positiveP; c1092ops_positiveQ] THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: missing_negative_longitudinal *)
let C1092OPS_MISSING_NEGATIVE_LONGITUDINAL = prove
 (`forall c s d t. c977cc_normal c s /\ &4 * s <= c /\ c977cc_normal d t /\ &252 / &373 <= t
     ==> &1 / &200 <= &1 - (&2 - d - t + (&11 / &25) * d * t) * c -
                      (&1 + d - t - (&11 / &25) * d pow 2) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MMNCE_LARGE_SUM) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&275 / &373`; `&252 / &373`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN C1092OPS_NORMAL_TAC THEN
  SUBGOAL_THEN `d * t <= &1 / &2` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `d - t:real`]; ALL_TAC] THEN
  C1092OPS_PROD `&0 <= (d - t) * (d + t)` THEN
  SUBGOAL_THEN `&1 / &2 <= d * d` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092OPS_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 - d - t + (&11 / &25) * d * t <= &81 / &100 /\
                &1 + d - t - (&11 / &25) * d pow 2 <= &17 / &20` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN C1092OPS_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&24 / &25`; `&1 / &4`; `c:real`; `s:real`; `&199 / &200`] C1092NPP_NORM_LE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  C1092OPS_PROD `&0 <= (&81 / &100 - (&2 - d - t + (&11 / &25) * d * t)) * c` THEN
  C1092OPS_PROD `&0 <= (&17 / &20 - (&1 + d - t - (&11 / &25) * d pow 2)) * s` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092OPS_LP_TAC);;
