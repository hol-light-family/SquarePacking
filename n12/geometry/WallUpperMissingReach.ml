(* ========================================================================= *)
(* Port of Compact/Geometry/WallUpperMissingReach.lean (Jatloe, N12-jatloe).  *)
(* A lower missing wall point and an upper missing central marker force the  *)
(* point (1,64/25).  exists_positive_frame is WCB_EXISTS_POSITIVE_FRAME,     *)
(* positive_frame_wall_bounds is TSS_POSITIVE_FRAME_WALL_BOUNDS, and         *)
(* short_projections is WFP_SHORT_PROJECTIONS.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallLowerCenterBarrier.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let WUMR_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: positive_point (private) *)
let WUMR_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 <= c /\ &0 <= s /\ &0 <= c * u - s * (v + a) /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&1) (&64 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c * s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c + s` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c + s <= &10 / &7` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + (&41 / &50) * c * s <= c + s` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&10 / &7 - (c + s)) * ((c + s) - &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  WUMR_UNFOLD_TAC `linside c s u v a (&457 / &500) (&2)` THEN
  WUMR_UNFOLD_TAC `linside c s u v a (&1) (&12 / &5)` THEN
  MAP_EVERY (fun (x,y) ->
    MP_TAC(SPECL [`c:real`; `s:real`; x; y] WFP_SHORT_PROJECTIONS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC)
   [`&0`,`&41 / &50`; `&13 / &20`,`&61 / &100`; `--(&13 / &20)`,`&21 / &100`] THEN
  SUBGOAL_THEN `c + s * (&87 / &50) <= u \/ --s + c * (&87 / &50) <= v` MP_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&1) (&87 / &50)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THENL
  [SUBGOAL_THEN `--s * (&33 / &20) + c * (&47 / &20) <= v` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&33 / &20) (&47 / &20)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC;
   SUBGOAL_THEN `c + s * (&64 / &25) < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= s * (v - (--s + c * (&87 / &50))) /\
      &0 < (a - &1) * (c + s) /\
      &0 <= c * ((c + s * (&64 / &25)) - (u + a))` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC]);;

(* Lean: point *)
let WUMR_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&1) (&64 / &25)`,
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
     is_iff(snd(strip_forall(concl th))) then REWRITE_TAC[GSYM th] THEN ASSUME_TAC th
     else NO_TAC) THEN
  MATCH_MP_TAC WUMR_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `a * (c' + s') / &2 <= lcx c s u v a` THEN
  UNDISCH_TAC `lcx c' s' u' v' a = lcx c s u v a` THEN
  REWRITE_TAC[lcx] THEN REAL_ARITH_TAC);;
