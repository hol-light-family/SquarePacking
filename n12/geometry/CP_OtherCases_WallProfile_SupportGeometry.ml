(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/WallProfile/SupportGeometry.lean    *)
(* (N12Compact.Completion.OtherCases.WallProfile).  Frame bookkeeping and    *)
(* exact support values; Lean `upper q nx ny` is ABT_upper.                  *)
(* turnFrame (c,s,u,v,a) = (--s, c, v, --u - a, a).                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: upper_in_bands *)
let OCWPSG_UPPER_IN_BANDS = prove
 (`forall c s u v a nx ny.
      ABT_upper c s u v a nx ny =
      (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2) +
      a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))`,
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: upper_turnFrame *)
let OCWPSG_UPPER_TURNFRAME = prove
 (`forall c s u v a nx ny.
      ABT_upper (--s) c v (--u - a) a nx ny = ABT_upper c s u v a nx ny`,
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `nx * --s + ny * c = --nx * s + ny * c`;
              REAL_ARITH `--nx * c + ny * --s = --(nx * c + ny * s)`; REAL_ABS_NEG] THEN
  REAL_ARITH_TAC);;

let OCWPSG_FRAME_TAC wits =
  MAP_EVERY EXISTS_TAC wits THEN
  ASM_REWRITE_TAC[OCWPSG_UPPER_TURNFRAME; linside] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN ASM_REAL_ARITH_TAC;;

(* Lean: positive_frame (with the private nonnegative_frame merged in) *)
let OCWPSG_POSITIVE_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 < c' /\ &0 <= s' /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           (forall nx ny. ABT_upper c' s' u' v' a' nx ny = ABT_upper c s u v a nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(forall nx ny. ABT_upper (--c) (--s) (--u - a) (--v - a) a nx ny = ABT_upper c s u v a nx ny) /\
    (forall nx ny. ABT_upper s (--c) (--v - a) u a nx ny = ABT_upper c s u v a nx ny)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `nx * --c + ny * --s = --(nx * c + ny * s)`;
                REAL_ARITH `--nx * --s + ny * --c = --(--nx * s + ny * c)`;
                REAL_ARITH `nx * s + ny * --c = --(--nx * s + ny * c)`;
                REAL_ARITH `--nx * --c + ny * s = nx * c + ny * s`; REAL_ABS_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < c /\ &0 <= s` THENL
   [MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c /\ s < &0` THENL
   [OCWPSG_FRAME_TAC [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`]; ALL_TAC] THEN
  ASM_CASES_TAC `c < &0 /\ s <= &0` THENL
   [MAP_EVERY EXISTS_TAC [`--c:real`; `--s:real`; `--u - a:real`; `--v - a:real`; `a:real`] THEN
    ASM_REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN
    REPEAT GEN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c <= &0 /\ &0 < s` THENL
   [MAP_EVERY EXISTS_TAC [`s:real`; `--c:real`; `--v - a:real`; `u:real`; `a:real`] THEN
    ASM_REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN
    REPEAT GEN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c = &0 /\ s = &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: downward_upper *)
let OCWPSG_DOWNWARD_UPPER = prove
 (`forall cq sq uq vq aq c s.
      &0 <= cq /\ &0 <= sq /\ &0 <= c /\ &0 <= s
      ==> ABT_upper cq sq uq vq aq c (--s) =
          (c * cq - s * sq) * uq - (c * sq + s * cq) * vq +
          aq * max (c * cq - s * sq) (&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `&0 <= c * sq + s * cq` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `c * cq + --s * sq = c * cq - s * sq`;
              REAL_ARITH `--c * sq + --s * cq = --(c * sq + s * cq)`; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  ASM_CASES_TAC `&0 <= c * cq - s * sq` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x /\ max x (&0) = x`;
               REAL_ARITH `~(&0 <= x) ==> abs x = --x /\ max x (&0) = &0`] THEN
  REAL_ARITH_TAC);;
