(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/BernsteinQuartic.lean               *)
(* (namespace N12Compact.CommonCases.BernsteinQuartic).                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: value (definition) *)
let ccbq_value = new_definition
 `ccbq_value (z:real) b0 b1 b2 b3 b4 =
    b0 * (&1 - z) pow 4 + &4 * b1 * z * (&1 - z) pow 3 +
    &6 * b2 * z pow 2 * (&1 - z) pow 2 + &4 * b3 * z pow 3 * (&1 - z) + b4 * z pow 4`;;

(* Lean: positive *)
let CCBQ_POSITIVE = prove
 (`forall z b0 b1 b2 b3 b4.
     &0 <= z /\ z <= &1 /\ &0 < b0 /\ &0 < b1 /\ &0 < b2 /\ &0 < b3 /\ &0 < b4
     ==> &0 < ccbq_value z b0 b1 b2 b3 b4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ccbq_value] THEN
  SUBGOAL_THEN `&0 <= &1 - z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b0 * (&1 - z) pow 4 + b4 * z pow 4` ASSUME_TAC THENL
   [ASM_CASES_TAC `z = &1` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 * b1 * z * (&1 - z) pow 3 /\
                &0 <= &6 * b2 * z pow 2 * (&1 - z) pow 2 /\
                &0 <= &4 * b3 * z pow 3 * (&1 - z)` MP_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;
