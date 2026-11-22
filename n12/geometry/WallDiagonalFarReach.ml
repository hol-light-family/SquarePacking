(* ========================================================================= *)
(* Port of Compact/Geometry/WallDiagonalFarReach.lean (Jatloe, N12-jatloe).   *)
(* A diagonal foreign corner seed pushes a positive canonical left wall to   *)
(* height 2.86.  positive_frame_wall_bounds is TSS_POSITIVE_FRAME_WALL_BOUNDS*)
(* and short_projections is WFP_SHORT_PROJECTIONS.                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallStrongerLowerReach.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let WDFR_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: margin (private) *)
let WDFR_MARGIN = prove
 (`forall c s. c977cc_normal c s ==> &0 <= c + s - &1 - (&9 / &10) * c * s + (&6 / &25) * s pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(&1 / &2) * s * s <= &1 - c` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `&1 - c`]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - c <= (&3 / &5) * s * s` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1 - c) * ((&3 / &5) * c - &2 / &5)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s * ((&1 - c) - (&1 / &2) * s * s) /\
                &0 <= s * ((s - &2 / &5) * (s - &2 / &5))` MP_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: point *)
let WDFR_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c s /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&19 / &25) (&49 / &25) /\
     ~linside c s u v a (&3 / &2) (&2)
     ==> linside c s u v a (&1) (&143 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    TSS_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN MESON_TAC[];
   STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= c * u - s * (v + a)` ASSUME_TAC THENL
  [UNDISCH_TAC `a * (c + s) / &2 <= lcx c s u v a` THEN REWRITE_TAC[lcx] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  WDFR_UNFOLD_TAC `linside c s u v a (&457 / &500) (&2)` THEN
  WDFR_UNFOLD_TAC `linside c s u v a (&1) (&12 / &5)` THEN
  MAP_EVERY (fun (x,y) ->
    MP_TAC(SPECL [`c:real`; `s:real`; x; y] WFP_SHORT_PROJECTIONS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC)
   [`&6 / &25`,`&9 / &10`; `&37 / &50`,`&1 / &25`; `--(&1 / &2)`,`&43 / &50`] THEN
  SUBGOAL_THEN `(&19 / &25) * c + (&49 / &25) * s <= u \/
                --(&19 / &25) * s + (&49 / &25) * c <= v` MP_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&19 / &25) (&49 / &25)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THENL
  [SUBGOAL_THEN `--(&3 / &2) * s + &2 * c <= v` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&3 / &2) (&2)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC;
   SUBGOAL_THEN `c + (&143 / &50) * s < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`] WDFR_MARGIN) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&0 <= s * (v - (--(&19 / &25) * s + (&49 / &25) * c)) /\
      &0 < (a - &1) * (c + s) /\
      &0 <= c * ((c + (&143 / &50) * s) - (u + a))` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 <= c * u - s * (v + a)` THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC]);;
