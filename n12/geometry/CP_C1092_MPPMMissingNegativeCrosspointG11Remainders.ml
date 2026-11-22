(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointG11-        *)
(* Remainders.lean (namespace N12Compact.C1092MPPMMissingNegativeCrosspoint- *)
(* Support).  Three constant quadratic-arc remainders for the missing-       *)
(* negative G11 proof.  QuadraticArc remainder / X / Y / Z / sum3 / pair3 /  *)
(* triple3: c1092mpqa_*.  Tag C1092MNCGR_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryHalf.ml";;

(* Lean: zero_formula (private) *)
let C1092MNCGR_ZERO_FORMULA = prove
 (`forall a b C z r. c1092mpqa_remainder a b C (&0) z r =
     (a - C) + (--a - C) * (z pow 2 + r pow 2 + z pow 2 * r pow 2) - &2 * a * z * r +
     &2 * b * (z + r)`,
  REWRITE_TAC[c1092mpqa_remainder; c1092mpqa_X; c1092mpqa_Y; c1092mpqa_Z;
              c1092mpqa_sum3; c1092mpqa_pair3; c1092mpqa_triple3] THEN
  CONV_TAC REAL_RING);;

let C1092MNCGR_EXTRA = prove
 (`forall z r. &0 <= z pow 2 + r pow 2 + z pow 2 * r pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
  TRY (MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  TRY (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN REWRITE_TAC[REAL_LE_POW_2]);;

(* Lean: low_remainder *)
let C1092MNCGR_LOW_REMAINDER = prove
 (`forall z. &0 <= z /\ z <= &1 / &3
       ==> &0 <= c1092mpqa_remainder (&67 / &200) (--(&147 / &200)) (--(&123 / &100)) (&0) z (&1 / &3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092MNCGR_ZERO_FORMULA] THEN
  MP_TAC (SPECL [`z:real`; `&1 / &3`] C1092MNCGR_EXTRA) THEN
  UNDISCH_TAC `z <= &1 / &3` THEN UNDISCH_TAC `&0 <= z` THEN REAL_ARITH_TAC);;

(* Lean: high_remainder *)
let C1092MNCGR_HIGH_REMAINDER = prove
 (`forall z r. &0 <= z /\ z <= &5 / &12 /\ &0 <= r /\ r <= &5 / &12
       ==> &0 <= c1092mpqa_remainder (&173 / &200) (--(&101 / &200)) (--(&311 / &200)) (&0) z r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092MNCGR_ZERO_FORMULA] THEN
  MP_TAC (SPECL [`z:real`; `r:real`] C1092MNCGR_EXTRA) THEN
  SUBGOAL_THEN `z * r <= &5 / &12 * &5 / &12` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN NO_TAC ORELSE
    (MATCH_MP_TAC (REAL_ARITH `z * r <= (&5 / &12) * (&5 / &12) ==> z * r <= &5 / &12 * &5 / &12`) THEN
     MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`z <= &5 / &12`; `r <= &5 / &12`; `&0 <= z`; `&0 <= r`] THEN
  REAL_ARITH_TAC);;

let C1092MNCGR_SQ_LE = prove
 (`forall x k. &0 <= x /\ x <= k ==> x * x <= k * k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let C1092MNCGR_LOWER_SQ = prove
 (`forall x. &1 / &3 <= x ==> &10 / &9 <= &1 + x pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &3 * &1 / &3 <= x * x` MP_TAC THENL
   [MATCH_MP_TAC (REAL_ARITH `(&1 / &3) * (&1 / &3) <= x * x ==> &1 / &3 * &1 / &3 <= x * x`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* Lean: middle_remainder *)
let C1092MNCGR_MIDDLE_REMAINDER = prove
 (`forall q z r. &1 / &3 <= q /\ q <= &5 / &12 /\ &1 / &3 <= z /\ z <= &5 / &12 /\
           &1 / &3 <= r /\ r <= &5 / &12
       ==> &0 <= c1092mpqa_remainder (--(&33 / &40)) (--(&171 / &200)) (--(&123 / &100)) q z r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &9 <= q * z /\ &1 / &9 <= q * r /\ &1 / &9 <= z * r` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    MATCH_MP_TAC (REAL_ARITH `(&1 / &3) * (&1 / &3) <= x ==> &1 / &9 <= x`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &3 <= c1092mpqa_pair3 q z r` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpqa_pair3] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092mpqa_triple3 q z r /\ c1092mpqa_triple3 q z r <= &125 / &1728`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpqa_triple3] THEN CONJ_TAC THENL
     [REPEAT (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN RASM_ARITH_TAC;
      MATCH_MP_TAC (REAL_ARITH `q * z * r <= ((&5 / &12) * (&5 / &12)) * (&5 / &12) ==> q * z * r <= &125 / &1728`) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL2 THEN RASM_ARITH_TAC;
        RASM_ARITH_TAC; RASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1000 / &729 <= c1092mpqa_Z q z r` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpqa_Z] THEN
    MP_TAC (SPEC `q:real` C1092MNCGR_LOWER_SQ) THEN MP_TAC (SPEC `z:real` C1092MNCGR_LOWER_SQ) THEN
    MP_TAC (SPEC `r:real` C1092MNCGR_LOWER_SQ) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC (REAL_ARITH `((&10 / &9) * (&10 / &9)) * (&10 / &9) <= x ==> &1000 / &729 <= x`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC REAL_LE_MUL2 THEN RASM_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC (SPECL [`c1092mpqa_triple3 q z r`; `&125 / &1728`] C1092MNCGR_SQ_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC (SPECL [`c1092mpqa_pair3 q z r - &1 / &3`; `c1092mpqa_pair3 q z r + &1 / &3`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC (SPECL [`c1092mpqa_triple3 q z r`; `c1092mpqa_pair3 q z r`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC (SPEC `c1092mpqa_sum3 q z r - &57 / &55` REAL_LE_POW_2) THEN DISCH_TAC THEN
  REWRITE_TAC[c1092mpqa_remainder; c1092mpqa_X; c1092mpqa_Y] THEN
  REPEAT DISCH_TAC THEN RASM_ARITH_TAC);;
