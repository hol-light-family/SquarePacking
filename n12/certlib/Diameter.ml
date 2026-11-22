(* ========================================================================= *)
(* Port of source/S12/Diameter.lean (Jatloe, N12-jatloe).                    *)
(* Markers (source/S12/Markers.lean) are the Phase-1 `marker k : real^2`     *)
(* (n12/phase1/markers.ml, same order 0..15).                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: inside_distance_bound *)
let DIA_INSIDE_DISTANCE_BOUND = prove
 (`forall c s u v a x y x' y'.
     c * c + s * s = &1 /\ &0 < a /\
     linside c s u v a x y /\ linside c s u v a x' y'
     ==> (x - x') pow 2 + (y - y') pow 2 < &2 * a pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x - x') pow 2 + (y - y') pow 2 =
     ((c * x + s * y) - (c * x' + s * y')) pow 2 +
     ((--s * x + c * y) - (--s * x' + c * y')) pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ABBREV_TAC `du = (c * x + s * y) - (c * x' + s * y')` THEN
  ABBREV_TAC `dv = (--s * x + c * y) - (--s * x' + c * y')` THEN
  SUBGOAL_THEN `&0 < a - du /\ &0 < a + du /\ &0 < a - dv /\ &0 < a + dv`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["du"; "dv"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN NLIN_TAC []);;

(* Lean: normalized_diameter_bound *)
let DIA_NORMALIZED_DIAMETER_BOUND = prove
 (`forall c s u v a x y x' y'.
     c * c + s * s = &1 /\ &0 < a /\ a <= &1001 / &1000 /\
     linside c s u v a x y /\ linside c s u v a x' y'
     ==> (x - x') pow 2 + (y - y') pow 2 < &2000000 / &982081`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `x:real`; `y:real`; `x':real`; `y':real`] DIA_INSIDE_DISTANCE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`(x - x') pow 2 + (y - y') pow 2`,`d:real`) THEN
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: Owns *)
let owns = new_definition
 `owns (c:real) s u v a i <=> linside c s u v a (marker i$1) (marker i$2)`;;
