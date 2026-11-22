(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareANarrow.lean (Jatloe N12).             *)
(* The forced point (2,5/2) for every positive frame once (3,5/2) is known   *)
(* to lie outside A.                                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareAForced.ml";;

(* Lean: point_of_higher_R *)
let FSAN_POINT_OF_HIGHER_R = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\
      lclosed c s u v a (&2) (&113 / &50) /\
      lclosed c s u v a (&113 / &50) (&2) /\
      lclosed c s u v a (&47 / &20) (&47 / &20) /\
      ~linside c s u v a (&33 / &20) (&33 / &20) /\
      ~linside c s u v a (&47 / &20) (&33 / &20) /\
      ~linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&3) (&12 / &5) /\
      ~linside c s u v a (&3) (&5 / &2)
      ==> linside c s u v a (&2) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [MATCH_MP_TAC FSAF_AXIS_POINT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&20 * s <= &99 * c` THENL
   [MATCH_MP_TAC FSAF_POSITIVE_WIDE_POINT THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `~linside c s u v a (&33 / &20) (&33 / &20)` (K ALL_TAC) THEN
  UNDISCH_THEN `~linside c s u v a (&3) (&12 / &5)` (K ALL_TAC) THEN
  UNDISCH_THEN `~(s = &0)` (K ALL_TAC) THEN
  FSAF_SP_TAC `-- &7 / &20` `&17 / &20` THEN
  FSAF_SP_TAC `&7 / &20` `&3 / &20` THEN
  SUBGOAL_THEN `s <= &1 /\ &7 / &10 * (c + s) <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - s:real`; SQ_NONNEG `c:real`];
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[lclosed; linside] THEN REAL_ARITH_TAC);;
