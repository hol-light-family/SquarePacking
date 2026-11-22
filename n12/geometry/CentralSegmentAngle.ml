(* ========================================================================= *)
(* Port of Compact/Geometry/CentralSegmentAngle.lean (Jatloe N12).            *)
(* A continuous angle exclusion from four owned points.                      *)
(* ClosedPointExclusion.closed_segment / outside_of_closed are               *)
(* LCLOSED_SEGMENT / OUTSIDE_OF_CLOSED (p2_base.ml).                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: exclude_small_nonnegative *)
let CSA_EXCLUDE_SMALL_NONNEGATIVE = prove
 (`forall cQ sQ uQ vQ aQ cA sA uA vA aA.
     cQ * cQ + sQ * sQ = &1 /\ &0 < aQ /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     &0 < cQ /\ &0 <= sQ /\ sQ <= cQ / &2 /\
     linside cQ sQ uQ vQ aQ (&33 / &20) (&33 / &20) /\
     linside cQ sQ uQ vQ aQ (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&2) (&87 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     ldisj cQ sQ uQ vQ aQ cA sA uA vA aA
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exists t. cQ * t = &17 / &50 * sQ /\ &0 <= t /\ t <= &17 / &100`
    STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `&17 / &50 * (sQ / cQ)` THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_LT_IMP_LE;
                 REAL_ARITH `&0 <= &17 / &50`] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_FIELD `&0 < c ==> c * (k * (s / c)) = k * s`];
      MATCH_MP_TAC(REAL_ARITH `x <= &1 / &2 ==> &17 / &50 * x <= &17 / &100`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `lclosed cA sA uA vA aA (&2 + t) (&87 / &50 + t)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&2 + t = (&1 - &50 / &13 * t) * &2 + (&50 / &13 * t) * (&113 / &50) /\
      &87 / &50 + t = (&1 - &50 / &13 * t) * (&87 / &50) + (&50 / &13 * t) * &2`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC LCLOSED_SEGMENT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aQ:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `&2 + t`; `&87 / &50 + t`] OUTSIDE_OF_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM ldisj]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sQ * t /\ &0 <= sQ * (&18 / &100 - t) /\
                &0 <= (cQ - &2 * sQ) * (&9 * cQ + &17 * sQ)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cQ * (sQ * t) = &17 / &50 * sQ * sQ` ASSUME_TAC THENL
   [MP_TAC(AP_TERM `(*) (sQ:real)` (ASSUME `cQ * t = &17 / &50 * sQ`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sQ * t <= &9 / &100 * cQ - &1 / &100 * sQ` ASSUME_TAC THENL
   [NLIN_TAC []; ALL_TAC] THEN
  UNDISCH_TAC `linside cQ sQ uQ vQ aQ (&33 / &20) (&33 / &20)` THEN
  UNDISCH_TAC `linside cQ sQ uQ vQ aQ (&2) (&113 / &50)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: angle_gap *)
let CSA_ANGLE_GAP = prove
 (`forall cQ sQ uQ vQ aQ cA sA uA vA aA.
     cQ * cQ + sQ * sQ = &1 /\ &0 < aQ /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     &0 < cQ /\
     linside cQ sQ uQ vQ aQ (&33 / &20) (&33 / &20) /\
     linside cQ sQ uQ vQ aQ (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&2) (&87 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     ldisj cQ sQ uQ vQ aQ cA sA uA vA aA
     ==> sQ < &0 \/ cQ / &2 < sQ`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aQ:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CSA_EXCLUDE_SMALL_NONNEGATIVE) THEN
  ASM_REWRITE_TAC[]);;
