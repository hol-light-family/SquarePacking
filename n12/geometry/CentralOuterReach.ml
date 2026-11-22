(* ========================================================================= *)
(* Port of Compact/Geometry/CentralOuterReach.lean (Jatloe, N12-jatloe).      *)
(* The complete elbow square reaches both outer arms.                        *)
(* short_projections is WFP_SHORT_PROJECTIONS; pullSwap is LINSIDE_PULLSW.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let COR_LINSIDE_RULE = CONV_RULE (REWR_CONV linside);;

(* Lean: positive_point (private) *)
let COR_POSITIVE_POINT = prove
 (`forall c s u v a x y.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&12 / &5) (&3) /\
     &47 / &20 <= x /\ &47 / &20 <= y /\
     x - &47 / &20 <= y - &33 / &20 /\
     (x - &47 / &20) pow 2 + (y - &33 / &20) pow 2 <= &1 /\
     (x - &33 / &20) pow 2 + (y - &47 / &20) pow 2 <= &1 /\
     (x - &3) pow 2 + (y - &12 / &5) pow 2 <= &1 /\
     (x - &12 / &5) pow 2 + (y - &3) pow 2 <= &1
     ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `linside c s u v a x y`) (concl th)
    then STRIP_ASSUME_TAC(COR_LINSIDE_RULE th) else NO_TAC)) THEN
  MAP_EVERY (fun (dx,dy) ->
    MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC)
   [`x - &47 / &20`, `y - &33 / &20`; `x - &33 / &20`, `y - &47 / &20`;
    `x - &3`, `y - &12 / &5`; `x - &12 / &5`, `y - &3`] THEN
  SUBGOAL_THEN `&0 <= c * (x - &47 / &20) /\ &0 <= s * (y - &47 / &20)`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN
  ASM_CASES_TAC `--s * (&47 / &20) + c * (&33 / &20) <= v` THENL
  [SUBGOAL_THEN `(&7 / &10) * (c + s) <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - s:real`; SQ_NONNEG `(&7 / &10) * (c + s) - &1`];
    ALL_TAC] THEN
   SUBGOAL_THEN `c * (&33 / &20) + s * (&47 / &20) <= u` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&33 / &20) (&47 / &20)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `&3 / &4`; `&13 / &20`] WFP_SHORT_PROJECTIONS) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
   SUBGOAL_THEN `v + a <= --s * (&12 / &5) + c * &3` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&12 / &5) (&3)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC;
   SUBGOAL_THEN `c * (&47 / &20) + s * (&33 / &20) <= u` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&47 / &20) (&33 / &20)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &20`; `&3 / &4`] WFP_SHORT_PROJECTIONS) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
   SUBGOAL_THEN `--s * &3 + c * (&12 / &5) <= v` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&3) (&12 / &5)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (c - s) * (x - &47 / &20) /\
                 &0 <= c * ((y - &33 / &20) - (x - &47 / &20))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC]);;

(* Lean: positive_points (private) *)
let COR_POSITIVE_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&12 / &5) (&3)
     ==> linside c s u v a (&47 / &20) (&53 / &20) /\
         linside c s u v a (&53 / &20) (&47 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC COR_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: points *)
let COR_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&12 / &5) (&3)
     ==> linside c s u v a (&47 / &20) (&53 / &20) /\
         linside c s u v a (&53 / &20) (&47 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match [] `forall x y. lclosed c s u v a x y <=> q`) (concl th))) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) then
     (RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th])
     else NO_TAC) THEN
  ASM_CASES_TAC `s' <= c'` THENL
  [MATCH_MP_TAC COR_POSITIVE_POINTS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   MP_TAC(SPECL [`s':real`; `c':real`; `u':real`; `--v' - a':real`; `a':real`]
     COR_POSITIVE_POINTS) THEN
   ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; MESON_TAC[]]]);;
