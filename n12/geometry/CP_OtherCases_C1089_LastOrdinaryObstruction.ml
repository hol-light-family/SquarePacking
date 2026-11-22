(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/LastOrdinaryObstruction.lean  *)
(* (N12Compact.Completion.OtherCases.C1089.LastOrdinaryObstruction).  The    *)
(* literal final northeast obstruction of C1089-SIMPLIFIED-PROOF section 5, *)
(* in the rigid chart (xi,eta) = (3-x, y-2).  Lean's r = (pullX q).translated *)
(* 1 2 is the explicit square (--c) s (u-3c-2s) (--v-a-3s+2c) a              *)
(* (OC1089LO_CHART).  EightPointObstruction.impossible is OCEPO_IMPOSSIBLE.  *)
(* Tag OC1089LO_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_EightPointObstruction.ml";;

(* the chart: r.Inside x y <=> q.Inside (3 - x) (2 + y) *)
let OC1089LO_CHART = prove
 (`forall c s u v a x y.
     linside (--c) s (u - &3 * c - &2 * s) (--v - a - &3 * s + &2 * c) a x y <=>
     linside c s u v a (&3 - x) (&2 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: eight_point_impossible *)
let OC1089LO_EIGHT_POINT_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&5 / &2) (&2) /\
     ~linside c s u v a (&3) (&3) /\
     ~linside c s u v a (&273 / &100) (&49 / &25) /\
     ~linside c s u v a (&64 / &25) (&3) /\
     ~linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&3) (&2)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--c:real`; `s:real`; `u - &3 * c - &2 * s`;
                `--v - a - &3 * s + &2 * c`; `a:real`] OCEPO_IMPOSSIBLE) THEN
  REWRITE_TAC[ocepo_input; OC1089LO_CHART] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: impossible *)
let OC1089LO_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&5 / &2) (&2) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&3) (&3) /\
     ~linside c s u v a (&273 / &100) (&49 / &25) /\
     ~linside c s u v a (&64 / &25) (&3) /\
     ~linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&3) (&2)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC OC1089LO_EIGHT_POINT_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  ASM_REWRITE_TAC[]);;
