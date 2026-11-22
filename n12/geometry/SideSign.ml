(* ========================================================================= *)
(* Port of Completion/Cases/C696/SideSign.lean (namespace S12).              *)
(* C696 side-owner sign in the arbitrary-rotation OpenSquare model.          *)
(* S12.exists_positive_frame is WCB_EXISTS_POSITIVE_FRAME,                   *)
(* positive_frame_wall_bounds is C977WC_POSITIVE_FRAME_WALL_BOUNDS,          *)
(* center_coordinates is LCENTRE_COORDS.  The private transposeSideSquare    *)
(* is the explicit square (s, c, u, --v - a, a), halfTurnSideSquare is       *)
(* (c, s, &4 * (c + s) - u - a, &4 * (c - s) - v - a, a).  Tag C696SS_.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/SideSignAlgebra.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;
needs "n12/geometry/C977WallChains.ml";;

let C696SS_ADJ_TAC =
  SUBGOAL_THEN `a / &2 <= c * (X - &1) + (&13 / &50) * s` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a / &2 <= s * (&87 / &50 - X)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `c:real`; `s:real`] C696SSA_ADJACENT_STRICT_OF_SUM_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`s:real`; `a / &2`; `c * (X - &1) + (&13 / &50) * s`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`c:real`; `a / &2`; `s * (&87 / &50 - X)`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;;
let C696SS_HOR_TAC =
  MP_TAC(SPECL [`a:real`; `s:real`; `c:real`] C696SSA_POSITIVE_HORIZONTAL_STRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `a / &2 <= s * (&1 - X) + (&13 / &50) * c` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`s:real`; `a * (c + s) / &2`; `X:real`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;;
(* Lean: side_owner_sign_positive_frame (private), with the centre abstracted to X, Y *)
let C696SS_CORE = prove
 (`forall c s u v a X Y. c * c + s * s = &1 /\ &0 <= c /\ &0 <= s /\ &1 < a /\
     a * (c + s) / &2 <= X /\ c * X + s * Y = u + a / &2 /\ --s * X + c * Y = v + a / &2 /\
     (u < c * &457 / &500 + s * &2 /\ c * &457 / &500 + s * &2 < u + a /\
      v < --s * &457 / &500 + c * &2 /\ --s * &457 / &500 + c * &2 < v + a) /\
     (u < c * &1 + s * &12 / &5 /\ c * &1 + s * &12 / &5 < u + a /\
      v < --s * &1 + c * &12 / &5 /\ --s * &1 + c * &12 / &5 < v + a) /\
     ~(u < c * &1 + s * &87 / &50 /\ c * &1 + s * &87 / &50 < u + a /\
      v < --s * &1 + c * &87 / &50 /\ --s * &1 + c * &87 / &50 < v + a) /\
     ~(u < c * &87 / &50 + s * &2 /\ c * &87 / &50 + s * &2 < u + a /\
      v < --s * &87 / &50 + c * &2 /\ --s * &87 / &50 + c * &2 < v + a)
     ==> &2 < Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s:real`] [`c <= &1`; `s <= &1`; `&0 < c + s`] THEN
  SUBGOAL_THEN `&0 <= c * (&2 - Y) /\ &0 <= s * (&2 - Y) /\ &0 <= s * (X - a * (c + s) / &2)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s * (&12 / &5 - &87 / &50) /\ &0 <= c * (&12 / &5 - &87 / &50) /\
                &0 <= s * (&87 / &50 - &457 / &500) /\ &0 <= c * (&87 / &50 - &457 / &500)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &1 + s * &87 / &50 <= u \/ --s * &1 + c * &87 / &50 <= v` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * &87 / &50 + s * &2 \/ --s * &87 / &50 + c * &2 <= v` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_neg (concl th)))) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST [ASM_REAL_ARITH_TAC; C696SS_ADJ_TAC; C696SS_HOR_TAC]);;

(* Lean: side_owner_sign_positive_frame (private) *)
let C696SS_SIDE_OWNER_SIGN_POSITIVE_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 <= c /\ &0 <= s /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y) /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&87 / &50) /\ ~linside c s u v a (&87 / &50) (&2)
     ==> &2 < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC C696SS_CORE THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `lcx c s u v a`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN ASM_REWRITE_TAC[]);;

(* Lean: c696_left_side_center_gt_two *)
let C696SS_LEFT_SIDE_CENTER_GT_TWO = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y) /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&87 / &50) /\ ~linside c s u v a (&87 / &50) (&2)
     ==> &2 < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] WCB_EXISTS_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `lcy c s u v a` then
    SUBST1_TAC(SYM th) else NO_TAC) THEN
  MATCH_MP_TAC C696SS_SIDE_OWNER_SIGN_POSITIVE_FRAME THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* Lean: transposeSideSquare_inside (private) *)
let C696SS_TRANSPOSE_INSIDE = prove
 (`forall c s u v a x y. linside s c u (--v - a) a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: transposeSideSquare_centerY (private) *)
let C696SS_TRANSPOSE_CENTERY = prove
 (`forall c s u v a. lcy s c u (--v - a) a = lcx c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: c696_bottom_side_center_gt_two *)
let C696SS_BOTTOM_SIDE_CENTER_GT_TWO = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y) /\
     linside c s u v a (&2) (&457 / &500) /\ linside c s u v a (&12 / &5) (&1) /\
     ~linside c s u v a (&87 / &50) (&1) /\ ~linside c s u v a (&2) (&87 / &50)
     ==> &2 < lcx c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM C696SS_TRANSPOSE_CENTERY] THEN
  MATCH_MP_TAC C696SS_LEFT_SIDE_CENTER_GT_TWO THEN
  ASM_REWRITE_TAC[C696SS_TRANSPOSE_INSIDE] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]);;

(* Lean: halfTurnSideSquare_inside (private) *)
let C696SS_HALFTURN_INSIDE = prove
 (`forall c s u v a x y. linside c s (&4 * (c + s) - u - a) (&4 * (c - s) - v - a) a x y <=>
                   linside c s u v a (&4 - x) (&4 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: halfTurnSideSquare_centerY, halfTurnSideSquare_centerX (private) *)
let C696SS_HALFTURN_CENTER = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcy c s (&4 * (c + s) - u - a) (&4 * (c - s) - v - a) a = &4 - lcy c s u v a /\
         lcx c s (&4 * (c + s) - u - a) (&4 * (c - s) - v - a) a = &4 - lcx c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING);;

let C696SS_HALFTURN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C696SS_HALFTURN_CENTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* Lean: c696_right_side_center_lt_two *)
let C696SS_RIGHT_SIDE_CENTER_LT_TWO = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> x <= &4 /\ y <= &4) /\
     linside c s u v a (&1543 / &500) (&2) /\ linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&3) (&113 / &50) /\ ~linside c s u v a (&113 / &50) (&2)
     ==> lcy c s u v a < &2`,
  C696SS_HALFTURN_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&4 * (c + s) - u - a`; `&4 * (c - s) - v - a`; `a:real`]
    C696SS_LEFT_SIDE_CENTER_GT_TWO) THEN
  ASM_REWRITE_TAC[C696SS_HALFTURN_INSIDE] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REAL_ARITH_TAC);;

(* Lean: c696_top_side_center_lt_two *)
let C696SS_TOP_SIDE_CENTER_LT_TWO = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> x <= &4 /\ y <= &4) /\
     linside c s u v a (&2) (&1543 / &500) /\ linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&113 / &50) (&3) /\ ~linside c s u v a (&2) (&113 / &50)
     ==> lcx c s u v a < &2`,
  C696SS_HALFTURN_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&4 * (c + s) - u - a`; `&4 * (c - s) - v - a`; `a:real`]
    C696SS_BOTTOM_SIDE_CENTER_GT_TWO) THEN
  ASM_REWRITE_TAC[C696SS_HALFTURN_INSIDE] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REAL_ARITH_TAC);;
