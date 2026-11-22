(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976MergedLeft/TopOnlyReach.lean    *)
(* (namespace N12Compact.Completion.OtherCases.C976MergedLeft).  The        *)
(* positive tip and the reach instance of OTHER-GEOMETRY Theorem 5.         *)
(* TopOnlyLeftPoint.*: OCTOLP_*; increasing_projection:                     *)
(* CCOS_INCREASING_PROJECTION; short_projections: WFP_SP;                   *)
(* C981CompletionCornerAdvance.upper_wall: C981CA_UPPER_WALL;               *)
(* ClosedFrames.positive_frame: CLF_POSITIVE_FRAME.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyLeftPoint.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: positive_tip *)
let OCC976MLTR_POSITIVE_TIP = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1) /\
      ~linside c s u v a (&1) (&1) /\
      (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
      ==> linside c s u v a (&13 / &500) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OCTOLP_SPEC_TAC [`&13 / &50`] THEN
  MP_TAC(SPEC_ALL OCTOLP_POSITIVE_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCTOLP_BAR_FACE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OCTOLP_CU_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&11 / &25`; `&487 / &500`]
    CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  OCTOLP_KEEP_TAC []);;

(* Lean: reach_positive (private) *)
let OCC976MLTR_REACH_POSITIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\
      s * (u + a) + c * (v + a) <= &1 /\
      linside c s u v a (&0) (&0) /\
      ~linside c s u v a (--(&13 / &500)) (&0) /\
      ~linside c s u v a (&0) (--(&19 / &50))
      ==> linside c s u v a (&4 / &5) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1 /\ &0 <= c * s` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [NLIN_TAC [SQ_NONNEG `s:real`]; NLIN_TAC [SQ_NONNEG `c:real`];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c + s` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (c + s) * (c + s) - &1` MP_TAC THENL
     [UNDISCH_TAC `&0 <= c * s` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c + s) * (c + s) < &1 * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `c + s <= &283 / &200` ASSUME_TAC THENL
   [MP_TAC(SPEC `c - s` REAL_LE_SQUARE) THEN DISCH_TAC THEN
    NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &207 / &250 * c * s <= c + s` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= ((c + s) - &1) * (&283 / &200 - (c + s))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 <= c * s` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `--(&13 / &500) * c <= u` THENL
   [SUBGOAL_THEN `v < --(&4 / &5) * s` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= s * (u - --(&13 / &500) * c) /\
                    &0 <= c * (v + &4 / &5 * s) /\ &0 < (a - &1) * (c + s)` MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
        ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    OCTOLP_KEEP_TAC [];
    ALL_TAC] THEN
  OCTOLP_STEP `v + a <= &13 / &500 * s` [`~linside c s u v a (--(&13 / &500)) (&0)`] THEN
  MP_TAC(WFP_SP `&19 / &50` `&13 / &500`) THEN MP_TAC(WFP_SP `&4 / &5` `&19 / &50`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  OCTOLP_STEP `--(&19 / &50) * s <= u` [`~linside c s u v a (&0) (--(&19 / &50))`] THEN
  OCTOLP_KEEP_TAC []);;

(* Lean: top_only_reach *)
let OCC976MLTR_TOP_ONLY_REACH = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      (forall x y. linside c s u v a x y ==> y <= &1) /\
      linside c s u v a (&0) (&0) /\
      ~linside c s u v a (--(&13 / &500)) (&0) /\
      ~linside c s u v a (&0) (--(&19 / &50))
      ==> linside c s u v a (&4 / &5) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th) &&
       length(fst(strip_forall(concl th))) = 2 && is_eq(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`] C981CA_UPPER_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC OCC976MLTR_REACH_POSITIVE THEN ASM_REWRITE_TAC[]);;
