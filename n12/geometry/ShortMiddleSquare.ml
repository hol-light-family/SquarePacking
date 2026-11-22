(* ========================================================================= *)
(* Port of Compact/Geometry/ShortMiddleSquare.lean                           *)
(* (N12Compact.ShortMiddleSquare).  A square of side > 1 cannot lie, on one  *)
(* common separating axis, between two actual points less than 1 apart.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: impossible *)
let SMS_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD cB sB uB vB aB x y z w u v.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     u pow 2 + v pow 2 = &1 /\ &1 < aD /\
     linside cO sO uO vO aO x y /\
     linside cB sB uB vB aB z w /\
     (z - x) pow 2 + (w - y) pow 2 < &1 /\
     ABT_lower cD sD uD vD aD u v + aD <= ABT_upper cD sD uD vD aD u v /\
     ABT_upper cO sO uO vO aO u v <= ABT_lower cD sD uD vD aD u v /\
     ABT_upper cD sD uD vD aD u v <= ABT_lower cB sB uB vB aB u v
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `x:real`; `y:real`; `u:real`; `v:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `z:real`; `w:real`; `u:real`; `v:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u * (z - x) + v * (w - y)) pow 2 + (u * (w - y) - v * (z - x)) pow 2 < &1`
  MP_TAC THENL
   [SUBGOAL_THEN `(u * (z - x) + v * (w - y)) pow 2 + (u * (w - y) - v * (z - x)) pow 2 =
                  ((z - x) pow 2 + (w - y) pow 2) * (u pow 2 + v pow 2)` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ASM_REWRITE_TAC[REAL_MUL_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < u * (z - x) + v * (w - y)` MP_TAC THENL
   [ABT_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`u * (z - x) + v * (w - y)`,`p:real`) THEN
  SPEC_TAC(`u * (w - y) - v * (z - x)`,`q:real`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN REPEAT DISCH_TAC THEN
  NLIN_TAC [SQ_NONNEG `q:real`]);;
