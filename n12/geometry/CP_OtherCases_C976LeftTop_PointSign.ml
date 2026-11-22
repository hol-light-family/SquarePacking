(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/PointSign.lean          *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints).  The complete *)
(* nonpositive-frame argument in C976-LEFT-UPPER-POINTS section 1.  Square q *)
(* is c s u v a; Input is occ976lt_input; increasing_projection is           *)
(* CCOS_INCREASING_PROJECTION.  Tag OCC976PG_.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_PointScalars.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;

let OCC976PG_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: nonpositive_impossible *)
let OCC976PG_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     occ976lt_input c s u v a /\ s = --t /\ &0 < c /\ &0 <= t /\ t <= c ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[occ976lt_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c (--t) u v a (--(&43 / &500)) (&0)`;
    `linside c (--t) u v a (&13 / &20) (&7 / &20)`;
    `linside c (--t) u v a (&0) (&13 / &50)`] THEN
  SUBGOAL_THEN `(&3 / &7) * c < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCC976PG_MISS_TAC `~linside c (--t) u v a (&1 / &2) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `(&27 / &100) * c + (&1 / &25) * t < u + a` ASSUME_TAC THENL
   [ASM_CASES_TAC `t <= (&38 / &39) * c` THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `t:real`; `&27 / &100`; `&26 / &25`]
      CCOS_INCREASING_PROJECTION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
    SUBGOAL_THEN `v + a <= c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      OCC976PG_MISS_TAC `~linside c (--t) u v a (&0) (&1)`; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `&13 / &100`)) (concl th) then
      ASSUME_TAC(REWRITE_RULE[] (CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
        (SPEC `&1` th))) else NO_TAC) THEN
    SUBGOAL_THEN `--(&13 / &50) * c <= v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      OCC976PG_MISS_TAC `~linside c (--t) u v a (&0) (-- &13 / &50)`; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&6 * t - &5 * c) * (&6 * t + &5 * c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&63 / &50) * c < &1` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC []; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  OCC976PG_MISS_TAC `~linside c (--t) u v a (&27 / &100) (--(&1 / &25))`);;
