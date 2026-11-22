(* ========================================================================= *)
(* Port of Compact/Completion/C981/Charts.lean                                *)
(* (N12Compact.C981CompletionCharts).  Rigid coordinate charts of the same   *)
(* actual square, as maps of the 5-tuple (c,s,u,v,a):                        *)
(*   corner     (s, --c, u - c - &3 * s, v + s - &3 * c, a)                   *)
(*   top        (--c, s, u - &2 * c - &3 * s, --v - a - &2 * s + &3 * c, a)  *)
(*   shiftedTop (c, s, u - &2 * c - &3 * s, v + &2 * s - &3 * c, a)          *)
(* The side components are literally a (Lean: corner_side, top_side,         *)
(* shiftedTop_side); C981CH_*_SQUARE record the OpenSquare fields.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: corner, corner_side (structure fields) *)
let C981CH_CORNER_SQUARE = prove
 (`forall c s a. c * c + s * s = &1 /\ &0 < a ==> s * s + --c * --c = &1 /\ &0 < a /\ a = a`,
  REAL_ARITH_TAC);;

(* Lean: top, top_side (structure fields) *)
let C981CH_TOP_SQUARE = prove
 (`forall c s a. c * c + s * s = &1 /\ &0 < a ==> --c * --c + s * s = &1 /\ &0 < a /\ a = a`,
  REAL_ARITH_TAC);;

(* Lean: shiftedTop, shiftedTop_side (structure fields) *)
let C981CH_SHIFTEDTOP_SQUARE = prove
 (`forall c s a. c * c + s * s = &1 /\ &0 < a ==> c * c + s * s = &1 /\ &0 < a /\ a = a`,
  REAL_ARITH_TAC);;

(* Lean: inside_corner *)
let C981CH_INSIDE_CORNER = prove
 (`forall c s u v a x y.
     linside s (--c) (u - c - &3 * s) (v + s - &3 * c) a x y <=>
     linside c s u v a (&1 - y) (&3 + x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inside_top *)
let C981CH_INSIDE_TOP = prove
 (`forall c s u v a x y.
     linside (--c) s (u - &2 * c - &3 * s) (--v - a - &2 * s + &3 * c) a x y <=>
     linside c s u v a (&2 - x) (&3 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inside_shiftedTop *)
let C981CH_INSIDE_SHIFTEDTOP = prove
 (`forall c s u v a x y.
     linside c s (u - &2 * c - &3 * s) (v + &2 * s - &3 * c) a x y <=>
     linside c s u v a (&2 + x) (&3 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: corner_wall *)
let C981CH_CORNER_WALL = prove
 (`forall c s u v a. lcont c s u v a
     ==> forall x y. linside s (--c) (u - c - &3 * s) (v + s - &3 * c) a x y ==> y <= &1`,
  REWRITE_TAC[lcont; C981CH_INSIDE_CORNER] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&1 - y`; `&3 + x`]) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Lean: top_wall *)
let C981CH_TOP_WALL = prove
 (`forall c s u v a. lcont c s u v a
     ==> forall x y. linside (--c) s (u - &2 * c - &3 * s) (--v - a - &2 * s + &3 * c) a x y
               ==> y <= &1`,
  REWRITE_TAC[lcont; C981CH_INSIDE_TOP] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&2 - x`; `&3 + y`]) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Lean: shiftedTop_wall *)
let C981CH_SHIFTEDTOP_WALL = prove
 (`forall c s u v a. lcont c s u v a
     ==> forall x y. linside c s (u - &2 * c - &3 * s) (v + &2 * s - &3 * c) a x y ==> y <= &1`,
  REWRITE_TAC[lcont; C981CH_INSIDE_SHIFTEDTOP] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&2 + x`; `&3 + y`]) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;
