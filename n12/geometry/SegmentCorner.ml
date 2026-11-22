(* ========================================================================= *)
(* Port of Compact/Geometry/SegmentCorner.lean (Jatloe, N12-jatloe).          *)
(* A closed segment avoiding an open rectangle passes outside its corner.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: crossing_order *)
let SEGC_CROSSING_ORDER = prove
 (`forall lU hU lV hV u0 v0 u1 v1.
     u0 <= lU /\ lU < u1 /\ u1 < hU /\
     lV < v0 /\ v0 < hV /\ hV <= v1 /\
     (forall t. &0 <= t ==> t <= &1 ==>
        ~(lU < (&1 - t) * u0 + t * u1 /\
          (&1 - t) * u0 + t * u1 < hU /\
          lV < (&1 - t) * v0 + t * v1 /\
          (&1 - t) * v0 + t * v1 < hV))
     ==> (hV - v0) * (u1 - u0) <= (lU - u0) * (v1 - v0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < u1 - u0 /\ &0 < v1 - v0` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `a = (lU - u0) / (u1 - u0)` THEN
  ABBREV_TAC `b = (hV - v0) / (v1 - v0)` THEN
  SUBGOAL_THEN `a * (u1 - u0) = lU - u0 /\ b * (v1 - v0) = hV - v0`
  STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
   ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a /\ b <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(b - a) * ((u1 - u0) * (v1 - v0)) =
                (hV - v0) * (u1 - u0) - (lU - u0) * (v1 - v0)` ASSUME_TAC THENL
  [UNDISCH_TAC `a * (u1 - u0) = lU - u0` THEN
   UNDISCH_TAC `b * (v1 - v0) = hV - v0` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 < (u1 - u0) * (v1 - v0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < (b - a) * ((u1 - u0) * (v1 - v0))` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SPEC_TAC(`(u1 - u0) * (v1 - v0)`,`P:real`) THEN
   REPEAT STRIP_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a + b) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < ((a + b) / &2 - a) * (u1 - u0) /\
                &0 < (&1 - (a + b) / &2) * (u1 - u0) /\
                &0 < (a + b) / &2 * (v1 - v0) /\
                &0 < (b - (a + b) / &2) * (v1 - v0)` MP_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  UNDISCH_TAC `a * (u1 - u0) = lU - u0` THEN
  UNDISCH_TAC `b * (v1 - v0) = hV - v0` THEN
  UNDISCH_TAC `u1 < hU` THEN UNDISCH_TAC `lV < v0` THEN
  REAL_ARITH_TAC);;
