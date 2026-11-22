(* ========================================================================= *)
(* Port of Compact/Completion/C981/WallAdvance.lean                           *)
(* (N12Compact.C981CompletionWallAdvance).  An actual wall owner advances to *)
(* height 2.8.  exists_positive_frame is WCB_EXISTS_POSITIVE_FRAME,          *)
(* positive_frame_wall_bounds is TSS_POSITIVE_FRAME_WALL_BOUNDS and          *)
(* short_projections is WFP_SHORT_PROJECTIONS.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_WallScalars.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

let C981WA_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: positive_point (private) *)
let C981WA_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     &0 <= c * u - s * (v + a) /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&19 / &25) (&187 / &100) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&1) (&14 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981WS_WALL_ARC) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  MAP_EVERY (fun (x,y) ->
    MP_TAC(SPECL [`c:real`; `s:real`; x; y] WFP_SHORT_PROJECTIONS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC)
   [`&6 / &25`,`&93 / &100`; `--(&13 / &20)`,`&9 / &20`; `&13 / &20`,`&61 / &100`;
    `--(&6 / &25)`,`&13 / &100`] THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c + s` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  C981WA_UNFOLD_TAC `linside c s u v a (&457 / &500) (&2)` THEN
  C981WA_UNFOLD_TAC `linside c s u v a (&1) (&12 / &5)` THEN
  SUBGOAL_THEN `--s * (&19 / &25) + c * (&187 / &100) <= v ==> c + s * (&14 / &5) < u + a`
  ASSUME_TAC THENL
  [DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= s * (v - (--s * (&19 / &25) + c * (&187 / &100))) /\
                 &0 <= c * ((c + s * (&14 / &5)) - (u + a)) /\
                 &0 < (a - &1) * (c + s)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (&33 / &20) + s * (&47 / &20) < u + a
                ==> --s * (&33 / &20) + c * (&47 / &20) <= v` ASSUME_TAC THENL
  [DISCH_TAC THEN UNDISCH_TAC `~linside c s u v a (&33 / &20) (&47 / &20)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--s * (&19 / &25) + c * (&187 / &100) < v + a
                ==> c * (&19 / &25) + s * (&187 / &100) <= u \/
                    --s * (&19 / &25) + c * (&187 / &100) <= v` ASSUME_TAC THENL
  [DISCH_TAC THEN UNDISCH_TAC `~linside c s u v a (&19 / &25) (&187 / &100)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c + s * (&87 / &50) <= u \/ --s + c * (&87 / &50) <= v` MP_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&1) (&87 / &50)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THENL
  [SUBGOAL_THEN `--s * (&33 / &20) + c * (&47 / &20) <= v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
      can (find_term ((=) `&47 / &20`)) (concl th) then MATCH_MP_TAC th else NO_TAC) THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c * (&19 / &25) + s * (&187 / &100) <= u \/
                 --s * (&19 / &25) + c * (&187 / &100) <= v` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
      can (find_term ((=) `&187 / &100`)) (concl th) && is_disj(rand(concl th))
      then MATCH_MP_TAC th else NO_TAC) THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THENL
   [RASM_ARITH_TAC;
    SUBGOAL_THEN `c + s * (&14 / &5) < u + a` MP_TAC THENL
    [FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
       can (find_term ((=) `&14 / &5`)) (concl th) then MATCH_MP_TAC th else NO_TAC) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    RASM_ARITH_TAC];
   SUBGOAL_THEN `c * (&19 / &25) + s * (&187 / &100) <= u \/
                 --s * (&19 / &25) + c * (&187 / &100) <= v` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
      can (find_term ((=) `&187 / &100`)) (concl th) && is_disj(rand(concl th))
      then MATCH_MP_TAC th else NO_TAC) THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THENL
   [ASM_CASES_TAC `(&53 / &50) * c <= &1` THENL
    [RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`] C981WS_SMALL_PROJECTION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `--s * (&33 / &20) + c * (&47 / &20) <= v` ASSUME_TAC THENL
    [FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
       can (find_term ((=) `&47 / &20`)) (concl th) then MATCH_MP_TAC th else NO_TAC) THEN
     RASM_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `c + s * (&14 / &5) < u + a` MP_TAC THENL
    [FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
       can (find_term ((=) `&14 / &5`)) (concl th) then MATCH_MP_TAC th else NO_TAC) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    RASM_ARITH_TAC]]);;

(* Lean: point *)
let C981WA_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&19 / &25) (&187 / &100) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&1) (&14 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  SUBGOAL_THEN `forall x y. linside c' s' u' v' a x y ==> &0 <= x /\ &0 <= y` ASSUME_TAC THENL
  [UNDISCH_TAC `lcont c s u v a` THEN ASM_REWRITE_TAC[lcont] THEN MESON_TAC[];
   ALL_TAC] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
    TSS_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) &&
     is_iff(snd(strip_forall(concl th))) then
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
     else NO_TAC) THEN
  MATCH_MP_TAC C981WA_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `a * (c' + s') / &2 <= lcx c s u v a` THEN
  UNDISCH_TAC `lcx c' s' u' v' a = lcx c s u v a` THEN
  REWRITE_TAC[lcx] THEN REAL_ARITH_TAC);;
