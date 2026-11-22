(* ========================================================================= *)
(* Port of Compact/Geometry/CentralBottomTransverse.lean (Jatloe, N12-jatloe;*)
(* namespace N12Compact.CentralBottomTransverse).  Genuine inward exclusion  *)
(* and the extended bottom-wall point remove the remaining transverse        *)
(* incoming axis.  Normal is c977cc_normal (C977CornerCubic.ml).  The        *)
(* OpenSquare invariants are explicit hypotheses.  Tag CBTR_.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: inward_cap *)
let CBTR_INWARD_CAP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ abs s <= c /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&3) (&87 / &50) /\
     c - &3 * s <= v /\ ~linside c s u v a (&3) (&2)
     ==> u + a <= &3 * c + &2 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
  [ASM_CASES_TAC `&0 < c` THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `c = &0 /\ s = &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside c s u v a (&3) (&2)` THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: point *)
let CBTR_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\ &1 < a /\
     linside c s u v a (&3) (&87 / &50) /\
     u + a <= &3 * c + &2 * s /\
     v + a < (&3 / &2) * c - &2 * s
     ==> linside c s u v a (&13 / &5) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal c s`)) THEN
  SUBGOAL_THEN `(c + s) pow 2 <= &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 / &5) * c + s < &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `(&2 / &5) * c + s <= (&7 / &10) * (c + s)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; NLIN_TAC []]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 / &2) * c + (&3 / &5) * s < &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `(&1 / &2) * c + (&3 / &5) * s <= (&11 / &20) * (c + s)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; NLIN_TAC []]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
  ASM_REAL_ARITH_TAC);;
