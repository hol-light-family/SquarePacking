(* ========================================================================= *)
(* Port of Compact/Geometry/CentralWingReach.lean (Jatloe N12).               *)
(* A foreign segment and a missing central marker force a central wing      *)
(* square to reach the next boundary point.                                  *)
(* canonical_frame: CLF_CANONICAL_FRAME;                                     *)
(* CentralSegmentAngle.exclude_small_nonnegative: CSA_EXCLUDE_SMALL_NONNEGATIVE.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CentralSegmentAngle.ml";;

let CWR_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* Lean: steep_impossible (private) *)
let CWR_STEEP_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ &0 <= s /\ s <= c /\ c / &2 <= s /\ a <= &1001 / &1000 /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&1) (&87 / &50)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (c - s) * (c + s) /\ &0 <= (&2 * s - c) * (&2 * c - s)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &7 / &10`; SQ_NONNEG `c + s - &4 / &3`]
   [`&7 / &10 <= c`; `&9 / &5 <= (c + s) * (c + s)`; `&4 / &3 <= c + s`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN CWR_ARITH_TAC);;

(* Lean: negative_point (private) *)
let CWR_NEGATIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ s < &0 /\ --c <= s /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&1) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  SUBGOAL_THEN `v + a <= --s * &33 / &20 + c * &47 / &20` ASSUME_TAC THENL
   [CWR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * (&9 * c + &35 * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CWR_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c + &11 * s`; SQ_NONNEG `c:real`; SQ_NONNEG `s:real`]
   [`((&17 / &20) * c - (&13 / &20) * s) * ((&17 / &20) * c - (&13 / &20) * s) <= &1`;
    `(&17 / &20) * c - (&13 / &20) * s <= &1`] THEN
  REWRITE_TAC[linside] THEN CWR_ARITH_TAC);;

(* Lean: point_low *)
let CWR_POINT_LOW = prove
 (`forall cQ sQ uQ vQ aQ cA sA uA vA aA.
     cQ * cQ + sQ * sQ = &1 /\ &0 < aQ /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     &1 < aQ /\ aQ <= &1001 / &1000 /\
     linside cQ sQ uQ vQ aQ (&33 / &20) (&33 / &20) /\
     linside cQ sQ uQ vQ aQ (&2) (&113 / &50) /\
     linside cQ sQ uQ vQ aQ (&1) (&87 / &50) /\
     ~linside cQ sQ uQ vQ aQ (&33 / &20) (&47 / &20) /\
     lclosed cA sA uA vA aA (&2) (&87 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     ldisj cQ sQ uQ vQ aQ cA sA uA vA aA
     ==> linside cQ sQ uQ vQ aQ (&1) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aQ:real`]
    CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a' (&1) (&3 / &2)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `a':real = aQ` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `linside c' s' u' v' aQ (&33 / &20) (&33 / &20) /\
    linside c' s' u' v' aQ (&2) (&113 / &50) /\
    linside c' s' u' v' aQ (&1) (&87 / &50) /\
    ~linside c' s' u' v' aQ (&33 / &20) (&47 / &20) /\
    ldisj c' s' u' v' aQ cA sA uA vA aA` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ldisj] THEN
    UNDISCH_TAC `ldisj cQ sQ uQ vQ aQ cA sA uA vA aA` THEN
    REWRITE_TAC[ldisj]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
  ASM_CASES_TAC `s' < &0` THENL
   [MATCH_MP_TAC CWR_NEGATIVE_POINT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s' <= c' / &2` THENL
   [MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `aQ:real`;
                  `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
      CSA_EXCLUDE_SMALL_NONNEGATIVE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `aQ:real`]
      CWR_STEEP_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: point *)
let CWR_POINT = prove
 (`forall cQ sQ uQ vQ aQ cA sA uA vA aA.
     cQ * cQ + sQ * sQ = &1 /\ &0 < aQ /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     &1 < aQ /\ aQ <= &1001 / &1000 /\
     linside cQ sQ uQ vQ aQ (&33 / &20) (&33 / &20) /\
     linside cQ sQ uQ vQ aQ (&2) (&113 / &50) /\
     linside cQ sQ uQ vQ aQ (&1) (&87 / &50) /\
     ~linside cQ sQ uQ vQ aQ (&33 / &20) (&47 / &20) /\
     lclosed cA sA uA vA aA (&2) (&87 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     ldisj cQ sQ uQ vQ aQ cA sA uA vA aA
     ==> linside cQ sQ uQ vQ aQ (&1) (&8 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aQ:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CWR_POINT_LOW) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `linside cQ sQ uQ vQ aQ (&1) (&87 / &50)` THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
