(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeMixedShallow.lean      *)
(* (N12Compact.Completion.OtherCases.C983.NegativeMixedShallow).  The        *)
(* shallow right-angle interval of the remaining mixed separator branch; the *)
(* Lean auxiliary v = b / (1 + a) is introduced as a witness of             *)
(* (1 + a) * v = b.  Tactics C983NRO_PROD / FACT / RING of                    *)
(* NegativeRightOwned.ml.  Tag C983NMS_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeRightOwned.ml";;

(* Lean: scalar *)
let C983NMS_SCALAR = prove
 (`forall c t a b H. &0 < c /\ &0 < t /\ t <= c /\ &0 < a /\ &0 <= b /\
     c pow 2 + t pow 2 = &1 /\ a pow 2 + b pow 2 = &1 /\
     b <= &9 / &41 /\ &4 / &5 * t <= H
     ==> &0 <= c * (&26 / &25 * a - b) + b * H - (a * c + b * t) * (&2 - a - b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exists v. (&1 + a) * v = b` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `b / (&1 + a)` THEN MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  C983NRO_FACT `&0 < &1 + a` THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [MATCH_MP_TAC C983NRO_NN_CANCEL THEN EXISTS_TAC `&1 + a` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  C983NRO_RING `(&1 + a) * (b * v - (&1 - a)) = &0` THEN
  SUBGOAL_THEN `b * v = &1 - a` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REAL_ENTIRE] o
      check (fun th -> concl th = `(&1 + a) * (b * v - (&1 - a)) = &0`)) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC C983NRO_UNIT_LE THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C983NRO_PROD `&0 <= b * (&1 - a)` THEN
  SUBGOAL_THEN `a + b < &6 / &5` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C983NRO_PROD `&0 <= (a + b - &6 / &5) * (a + b + &6 / &5)` THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  C983NRO_PROD `&0 <= v * (&1 - a)` THEN
  C983NRO_FACT `b / &2 <= v` THEN
  C983NRO_FACT `&1 / &2 <= &24 / &25 - &2 * b` THEN
  C983NRO_PROD `&0 <= (b * v) * ((&24 / &25 - &2 * b) - &1 / &2)` THEN
  C983NRO_PROD `&0 <= b * (v - b / &2)` THEN
  SUBGOAL_THEN `&0 <= &1 / &25 - b / &5 + b * v * (&24 / &25 - &2 * b)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [SQ_NONNEG `b / &2 - &1 / &5`]; ALL_TAC] THEN
  C983NRO_PROD `&0 <= c * (&1 / &25 - b / &5 + b * v * (&24 / &25 - &2 * b))` THEN
  C983NRO_PROD `&0 <= b * (c - t)` THEN
  C983NRO_PROD `&0 <= (b * (c - t)) * (&6 / &5 - (a + b))` THEN
  C983NRO_PROD `&0 <= b * (H - &4 / &5 * t)` THEN
  C983NRO_RING `c * (&26 / &25 * a - b) + b * (&4 / &5 * t) - (a * c + b * t) * (&2 - a - b) =
      c * (&1 / &25 - b / &5 + b * v * (&24 / &25 - &2 * b)) + b * (c - t) * (&6 / &5 - a - b)` THEN
  NLIN_TAC ~deg2:false []);;
