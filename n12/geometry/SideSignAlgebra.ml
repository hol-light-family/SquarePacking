(* ========================================================================= *)
(* Port of Completion/Cases/C696/SideSignAlgebra.lean (namespace             *)
(* C696SideSign).  Elementary algebra for the exact C696 side-owner sign     *)
(* lemma.  Purely scalar.  Tag C696SSA_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

let C696SSA_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN NLIN_TAC ~deg2:false [SQ_NONNEG `u:real`]; ALL_TAC]) tms;;

(* Lean: positive_horizontal_strict *)
let C696SSA_POSITIVE_HORIZONTAL_STRICT = prove
 (`forall a u v. &1 < a /\ &0 <= u /\ u <= &1 /\ &0 <= v /\ v <= &1
     ==> &2 * u + (&13 / &25) * v < a * (&1 + u * u + u * v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C696SSA_PROD_TAC [`&0 <= u * v`] THEN
  SUBGOAL_THEN `&0 <= (&1 - u) pow 2 + v * (u - &13 / &25)` ASSUME_TAC THENL
   [ASM_CASES_TAC `&13 / &25 <= u` THENL
     [C696SSA_PROD_TAC [`&0 <= v * (u - &13 / &25)`] THEN
      MP_TAC(SPEC `&1 - u` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      C696SSA_PROD_TAC [`&0 <= (&1 - v) * (&13 / &25 - u)`] THEN
      MP_TAC(SPEC `u - &1 / &2` REAL_LE_POW_2) THEN REWRITE_TAC[REAL_POW_2] THEN
      DISCH_TAC THEN NLIN_TAC ~deg2:false []]; ALL_TAC] THEN
  C696SSA_PROD_TAC [`&0 < (a - &1) * (&1 + u * u + u * v)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC ~deg2:false []);;

(* Lean: adjacent_bound *)
let C696SSA_ADJACENT_BOUND = prove
 (`forall u v. &0 <= u /\ u <= &1 /\ &0 <= v /\ v <= &1
     ==> (&37 / &25) * u * v + (&13 / &25) * v * v <= u + v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C696SSA_PROD_TAC [`&0 <= u * (&1 - v)`;
    `&0 <= v * ((&12 / &25) * (&1 - u) + (&13 / &25) * (&1 - v))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: adjacent_strict_of_sum_pos *)
let C696SSA_ADJACENT_STRICT_OF_SUM_POS = prove
 (`forall a u v. &1 < a /\ &0 <= u /\ u <= &1 /\ &0 <= v /\ v <= &1 /\ &0 < u + v
     ==> (&37 / &25) * u * v + (&13 / &25) * v * v < a * (u + v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real`; `v:real`] C696SSA_ADJACENT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C696SSA_PROD_TAC [`&0 < (a - &1) * (u + v)`] THEN NLIN_TAC ~deg2:false []);;

(* Lean: adjacent_strict *)
let C696SSA_ADJACENT_STRICT = prove
 (`forall a u v. &1 < a /\ &0 < u /\ u <= &1 /\ &0 < v /\ v <= &1
     ==> (&37 / &25) * u * v + (&13 / &25) * v * v < a * (u + v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C696SSA_ADJACENT_STRICT_OF_SUM_POS THEN ASM_REAL_ARITH_TAC);;
