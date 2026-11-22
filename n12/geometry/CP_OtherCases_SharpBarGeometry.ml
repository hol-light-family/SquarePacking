(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SharpBarGeometry.lean               *)
(* (namespace N12Compact.Completion.OtherCases.SharpBarGeometry).           *)
(* A closed vertex and a strict marker on opposite sides of a segment force *)
(* a strict crossing.  WallProfile.strict_closed_segment:                    *)
(* OCWPVG_STRICT_CLOSED_SEGMENT; pullSwap: LINSIDE_PULLSW / LCLOSED_PULLSW. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

(* Lean: horizontal_crossing *)
let OCSBG_HORIZONTAL_CROSSING = prove
 (`forall c s u v a X Y x0 y0 h lo hi.
      lclosed c s u v a X Y /\ linside c s u v a x0 y0 /\
      y0 < h /\ h < Y /\ lo <= X /\ X <= hi /\ lo <= x0 /\ x0 <= hi /\
      (forall x. lo <= x ==> x <= hi ==> ~linside c s u v a x h)
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `t = (Y - h) / (Y - y0)` THEN
  SUBGOAL_THEN `&0 < Y - y0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * (Y - y0) = Y - h` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ t < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) * Y + t * y0 = h` ASSUME_TAC THENL
   [UNDISCH_TAC `t * (Y - y0) = Y - h` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `X:real`; `Y:real`; `x0:real`; `y0:real`; `t:real`]
    OCWPVG_STRICT_CLOSED_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
  SUBGOAL_THEN `&0 <= (&1 - t) * (X - lo) /\ &0 <= t * (x0 - lo) /\
                &0 <= (&1 - t) * (hi - X) /\ &0 <= t * (hi - x0)` MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: closed_swap (private): LCLOSED_PULLSW *)
(* Lean: vertical_crossing *)
let OCSBG_VERTICAL_CROSSING = prove
 (`forall c s u v a X Y x0 y0 h lo hi.
      lclosed c s u v a X Y /\ linside c s u v a x0 y0 /\
      x0 < h /\ h < X /\ lo <= Y /\ Y <= hi /\ lo <= y0 /\ y0 <= hi /\
      (forall y. lo <= y ==> y <= hi ==> ~linside c s u v a h y)
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC OCSBG_HORIZONTAL_CROSSING THEN
  MAP_EVERY EXISTS_TAC [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`;
    `Y:real`; `X:real`; `y0:real`; `x0:real`; `h:real`; `lo:real`; `hi:real`] THEN
  ASM_REWRITE_TAC[LINSIDE_PULLSW; LCLOSED_PULLSW]);;
