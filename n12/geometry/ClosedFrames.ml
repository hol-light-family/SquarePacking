(* ========================================================================= *)
(* Port of Compact/Geometry/ClosedFrames.lean                                *)
(*                                                                           *)
(* turnFrame (c,s,u,v,a) = (--s, c, v, --u - a, a)  (S12.WallGeometry);      *)
(* its iterates are (--c,--s,--u-a,--v-a,a) and (s,--c,--v-a,u,a).           *)
(* "?r : OpenSquare" becomes an existential over the 5-tuple together with   *)
(* the OpenSquare invariants c'*c'+s'*s' = &1 and &0 < a'.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: closed_turnFrame *)
let CLF_CLOSED_TURNFRAME = prove
 (`forall c s u v a x y. lclosed (--s) c v (--u - a) a x y <=> lclosed c s u v a x y`,
  REWRITE_TAC[lclosed] THEN REAL_ARITH_TAC);;

(* Lean: closed_pullX *)
let CLF_CLOSED_PULLX = prove
 (`forall c s u v a x y. lclosed (--c) s (u - &4 * c) (--v - a - &4 * s) a x y <=>
                   lclosed c s u v a (&4 - x) y`,
  REWRITE_TAC[lclosed] THEN REAL_ARITH_TAC);;

let CLF_FRAME_TAC wits =
  MAP_EVERY EXISTS_TAC wits THEN
  REWRITE_TAC[linside; lclosed] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN ASM_REAL_ARITH_TAC;;

(* Lean: positive_frame (and the private nonnegative_frame) *)
let CLF_POSITIVE_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 < c' /\ &0 <= s' /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           (forall x y. lclosed c' s' u' v' a' x y <=> lclosed c s u v a x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 < c /\ &0 <= s` THENL
   [CLF_FRAME_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c /\ s < &0` THENL
   [CLF_FRAME_TAC [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`]; ALL_TAC] THEN
  ASM_CASES_TAC `c < &0 /\ s <= &0` THENL
   [CLF_FRAME_TAC [`--c:real`; `--s:real`; `--u - a:real`; `--v - a:real`; `a:real`];
    ALL_TAC] THEN
  ASM_CASES_TAC `c <= &0 /\ &0 < s` THENL
   [CLF_FRAME_TAC [`s:real`; `--c:real`; `--v - a:real`; `u:real`; `a:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `c = &0 /\ s = &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: canonical_frame *)
let CLF_CANONICAL_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 < c' /\ abs s' <= c' /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           (forall x y. lclosed c' s' u' v' a' x y <=> lclosed c s u v a x y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `s1 <= c1` THENL
   [MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`s1:real`; `--c1:real`; `--v1 - a1:real`; `u1:real`; `a1:real`] THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) then REWRITE_TAC[GSYM th] else NO_TAC)) THEN
    REWRITE_TAC[linside; lclosed] THEN REPEAT CONJ_TAC THEN
    REPEAT GEN_TAC THEN ASM_REAL_ARITH_TAC]);;
