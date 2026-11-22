(* ========================================================================= *)
(* Port of Compact/Completion/C981/Crosspoint.lean                            *)
(* (N12Compact.C981CompletionCrosspoint).  The all-angle one-sided central   *)
(* crosspoint lemma.  short_projections is WFP_SHORT_PROJECTIONS;            *)
(* exists_positive_frame is WCB_EXISTS_POSITIVE_FRAME.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

let C981CP_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: positive (private) *)
let C981CP_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&3) (&5 / &2)
     ==> linside c s u v a (&2) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (x,y) ->
    MP_TAC(SPECL [`c:real`; `s:real`; x; y] WFP_SHORT_PROJECTIONS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC)
   [`--(&7 / &20)`,`&17 / &20`; `&13 / &20`,`&3 / &4`; `--(&7 / &10)`,`&7 / &10`;
    `&7 / &20`,`&3 / &20`] THEN
  SUBGOAL_THEN `s <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  C981CP_UNFOLD_TAC `linside c s u v a (&2) (&113 / &50)` THEN
  C981CP_UNFOLD_TAC `linside c s u v a (&113 / &50) (&2)` THEN
  C981CP_UNFOLD_TAC `linside c s u v a (&47 / &20) (&47 / &20)` THEN
  SUBGOAL_THEN `(&47 / &20) * c + (&33 / &20) * s <= u \/
                --(&47 / &20) * s + (&33 / &20) * c <= v` MP_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&47 / &20) (&33 / &20)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THENL
  [SUBGOAL_THEN `--(&3) * s + (&12 / &5) * c <= v` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&3) (&12 / &5)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `&20 * s <= &99 * c` THENL
   [SUBGOAL_THEN `s + c / &10 <= &1` ASSUME_TAC THENL
    [SUBGOAL_THEN `(s + c / &10) * (s + c / &10) - &1 = (c / &100) * (&20 * s - &99 * c)`
     MP_TAC THENL
     [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     SUBGOAL_THEN `(c / &100) * (&20 * s - &99 * c) <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SPEC_TAC(`s + c / &10`,`w:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
     NLIN_TAC [SQ_NONNEG `w - &1`]; ALL_TAC] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `--(&3) * s + (&5 / &2) * c <= v` ASSUME_TAC THENL
    [UNDISCH_TAC `~linside c s u v a (&3) (&5 / &2)` THEN
     REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC];
   SUBGOAL_THEN `(&33 / &20) * c + (&47 / &20) * s <= u` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&33 / &20) (&47 / &20)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC]);;

(* Lean: point *)
let C981CP_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&3) (&5 / &2)
     ==> linside c s u v a (&2) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) &&
     is_iff(snd(strip_forall(concl th))) then
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
     else NO_TAC) THEN
  MATCH_MP_TAC C981CP_POSITIVE THEN ASM_REWRITE_TAC[]);;
