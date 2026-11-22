(* ========================================================================= *)
(* Port of Compact/Completion/C1092/RigidCharts.lean                          *)
(* (namespace N12Compact.C1092RigidCharts).                                  *)
(* The rigid charts act on the 5-tuple c s u v a:                           *)
(*   translate Q x0 y0 = (c, s, u - c*x0 - s*y0, v + s*x0 - c*y0, a)         *)
(*   opposite Q        = (c, s, --u - a, --v - a, a)                          *)
(*   swap Q            = (c, --s, v, u, a)                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: translate / opposite / swap (definitions: the OpenSquare invariants) *)
let C1092RC_CHARTS_SQUARE = prove
 (`forall c s u v a x0 y0.
     lsquare c s u v a
     ==> lsquare c s (u - c * x0 - s * y0) (v + s * x0 - c * y0) a /\
         lsquare c s (--u - a) (--v - a) a /\
         lsquare c (--s) v u a`,
  REWRITE_TAC[lsquare] THEN REAL_ARITH_TAC);;

(* Lean: inside_translate *)
let C1092RC_INSIDE_TRANSLATE = prove
 (`forall c s u v a x0 y0 x y.
     linside c s (u - c * x0 - s * y0) (v + s * x0 - c * y0) a x y <=>
     linside c s u v a (x + x0) (y + y0)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inside_opposite *)
let C1092RC_INSIDE_OPPOSITE = prove
 (`forall c s u v a x y.
     linside c s (--u - a) (--v - a) a x y <=> linside c s u v a (--x) (--y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inside_swap *)
let C1092RC_INSIDE_SWAP = prove
 (`forall c s u v a x y.
     linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
