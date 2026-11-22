(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/BottomBarSupport.lean               *)
(* (N12Compact.Completion.OtherCases.BottomBarSupport).  Exhaustive lower-   *)
(* support alternatives supplied by the actual bottom bar.                   *)
(* LowerCornerSupport.horizontal: OCLCS_HORIZONTAL; OutwardScalars.          *)
(* increasing_projection: CCOS_INCREASING_PROJECTION; turnFrame (c,s,u,v,a)  *)
(* = (--s, c, v, --u - a, a) (ClosedFrames.ml), whose inside set is that of  *)
(* the square (CCBBS_TURN_INSIDE).  q.s = -t is written s = --t.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_LowerCornerSupport.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: S12.turnFrame_inside (source/S12/WallGeometry) *)
let CCBBS_TURN_INSIDE = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCBBS_UNFOLD_TAC ts =
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t))) ts;;

(* a point of the excluded bar gives a face inequality *)
let CCBBS_AVOID_TAC x =
  FIRST_ASSUM(MP_TAC o SPEC x o check (is_forall o concl)) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: positive *)
let CCBBS_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ c <= &1 /\
     linside c s u v a (&13 / &50) (&0) /\
     u < (&4 / &5) * c - s /\
     (forall x. &13 / &50 <= x /\ x <= &4 / &5 ==> ~linside c s u v a x (--(&1)))
     ==> --(&13 / &50) * s - c <= v \/ --(&1) <= s * u + c * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `--(&13 / &50) * s - c <= v` THEN ASM_REWRITE_TAC[] THEN
  CCBBS_UNFOLD_TAC [`linside c s u v a (&13 / &50) (&0)`] THEN
  SUBGOAL_THEN `c * &13 / &50 - s <= u` ASSUME_TAC THENL
  [CCBBS_AVOID_TAC `&13 / &50`; ALL_TAC] THEN
  SUBGOAL_THEN `--s * &4 / &5 - c <= v` ASSUME_TAC THENL
  [CCBBS_AVOID_TAC `&4 / &5`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&13 / &50`; `&4 / &5`]
    OCLCS_HORIZONTAL) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
   FIRST [RASM_ARITH_TAC;
          GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]];
   REWRITE_TAC[]]);;

(* Lean: negative *)
let CCBBS_NEGATIVE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\ &0 <= u /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&13 / &50) (&0) /\
     (forall x. &13 / &50 <= x /\ x <= &4 / &5 ==> ~linside c s u v a x (--(&1)))
     ==> (&13 / &50) * t - c <= v /\
         ((&4 / &5) * t - c <= v \/ --(&1) <= --t * (u + a) + c * v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  CCBBS_UNFOLD_TAC [`linside c (--t) u v a (&7 / &20) (--(&7 / &20))`;
                    `linside c (--t) u v a (&13 / &50) (&0)`] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `&13 / &50`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
   UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `t * &13 / &50 - c <= v` ASSUME_TAC THENL
  [CCBBS_AVOID_TAC `&13 / &50`; ALL_TAC] THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(&4 / &5) * t - c <= v` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `u + a <= c * &4 / &5 + t` ASSUME_TAC THENL
  [CCBBS_AVOID_TAC `&4 / &5`; ALL_TAC] THEN
  MP_TAC(SPECL [`--(--t)`; `c:real`; `v:real`; `--u - a`; `a:real`; `&13 / &50`; `&4 / &5`]
    OCLCS_HORIZONTAL) THEN
  REWRITE_TAC[CCBBS_TURN_INSIDE] THEN REWRITE_TAC[REAL_NEG_NEG] THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN
   FIRST [RASM_ARITH_TAC;
          UNDISCH_TAC `c * c + --t * --t = &1` THEN CONV_TAC REAL_RING;
          GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]];
   RASM_ARITH_TAC]);;
