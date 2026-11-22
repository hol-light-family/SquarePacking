(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastWallPolynomials.lean                   *)
(* (N12Compact.C981CompletionLastWallPolynomials).  Three rational           *)
(* polynomial margins of the final right-wall argument.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: first *)
let C981LWP_FIRST = prove
 (`forall z. &0 <= z /\ z <= &27 / &100
       ==> --(&367 / &2500) - (&117 / &1000) * z + (&1637 / &625) * z pow 2 -
           (&883 / &1000) * z pow 3 < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (z * (&27 / &100 - z)) * (&1637 / &625 - (&883 / &1000) * (z + &27 / &100))`
  MP_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `z pow 3 = z * z * z`; REAL_POW_2] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: second *)
let C981LWP_SECOND = prove
 (`forall z. &1 / &4 <= z
       ==> &87 / &250 - (&187 / &100) * z + (&261 / &125) * z pow 2 -
           (&87 / &100) * z pow 3 < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (z - &1 / &4) * ((&87 / &100) * (z - &43 / &40) pow 2 + &63517 / &160000)`
  MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC(SPEC `z - &43 / &40` REAL_LE_POW_2) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `z pow 3 = z * z * z`; REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: third *)
let C981LWP_THIRD = prove
 (`forall z. &0 <= z /\ z <= &1
       ==> &29 / &250 - (&4 / &5) * z + (&471 / &250) * z pow 2 - z pow 3 > &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_gt] THEN
  REWRITE_TAC[REAL_ARITH `z pow 3 = z * z * z`; REAL_POW_2] THEN
  ASM_CASES_TAC `z <= &1 / &2` THENL
  [SUBGOAL_THEN `&0 <= (z * z) * (&1 / &2 - z)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(SPEC `z - &50 / &173` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
   SUBGOAL_THEN `&0 <= (z - &1 / &2) * ((&1 - z) * z)` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPEC `z - &1 / &2` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC]);;
