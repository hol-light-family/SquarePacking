(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/DerivedWalls.lean                   *)
(* (N12Compact.Completion.OtherCases.DerivedWalls).  A genuine forbidden    *)
(* line plus a strict point on one side supplies an actual half-plane bound *)
(* which then applies to every closed square point.  inside_segment is       *)
(* CES_INSIDE_SEGMENT, affine_endpoint_nonnegative is                       *)
(* SCAP_AFFINE_ENDPOINT_NONNEG.  Tag OCDW_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

(* Lean: vertical_right *)
let OCDW_VERTICAL_RIGHT = prove
 (`forall c s u v a x0 y0 h.
     linside c s u v a x0 y0 /\ h < x0 /\ (forall y. ~linside c s u v a h y)
     ==> forall x y. linside c s u v a x y ==> h <= x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < x0 - x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `x:real`; `y:real`; `x0:real`; `y0:real`; `(h - x) / (x0 - x)`]
    CES_INSIDE_SEGMENT) THEN
  SUBGOAL_THEN `(h - x) / (x0 - x) * (x0 - x) = h - x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = (h - x) / (x0 - x)` THEN
  SUBGOAL_THEN `(&1 - T0) * x + T0 * x0 = h` SUBST1_TAC THENL
   [UNDISCH_TAC `T0 * (x0 - x) = h - x` THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* Lean: closed_affine_bound *)
let OCDW_CLOSED_AFFINE_BOUND = prove
 (`forall c s u v a nx ny bound x0 y0 X Y.
     (forall x y. linside c s u v a x y ==> bound <= nx * x + ny * y) /\
     linside c s u v a x0 y0 /\ lclosed c s u v a X Y
     ==> bound <= nx * X + ny * Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= nx * X + ny * Y - bound ==> bound <= nx * X + ny * Y`) THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`&1`; `nx * x0 + ny * y0 - (nx * X + ny * Y)`] THEN
  REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(&1 - t) * X + t * x0`; `(&1 - t) * Y + t * y0`]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC OCWPVG_STRICT_CLOSED_SEGMENT THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;
