(* ========================================================================= *)
(* Port of source/S12/ConvexOverlap.lean (Jatloe, N12-jatloe).               *)
(* Points of R x R are HOL pairs real#real.  squareSet q is                  *)
(* sqset c s u v a (a set of pairs); P - A is psub P A.  Mathlib's           *)
(* Convex R on R x R is pconvex; convexHull R V (V a set of pairs) is        *)
(* pconvex_hull V, defined through Multivariate's `convex hull` on real^2.   *)
(* OverlapsAt q r A B is overlaps_at (sqset q) (sqset r) A B.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/Convex.ml";;

let psub = new_definition
 `psub (p:real#real) (q:real#real) = (FST p - FST q, SND p - SND q)`;;

(* Lean: squareSet *)
let sqset = new_definition
 `sqset c s u v a = {p:real#real | linside c s u v a (FST p) (SND p)}`;;

let IN_SQSET = prove
 (`forall c s u v a p. p IN sqset c s u v a <=> linside c s u v a (FST p) (SND p)`,
  REWRITE_TAC[sqset; IN_ELIM_THM]);;

(* Mathlib's Convex R S for S : Set (R x R) *)
let pconvex = new_definition
 `pconvex (S:real#real->bool) <=>
    forall p r a b. p IN S /\ r IN S /\ &0 <= a /\ &0 <= b /\ a + b = &1
              ==> (a * FST p + b * FST r, a * SND p + b * SND r) IN S`;;

let vec2 = new_definition `vec2 (p:real#real) = vector[FST p; SND p]:real^2`;;

(* Mathlib's convexHull R V for V : Set (R x R) *)
let pconvex_hull = new_definition
 `pconvex_hull (V:real#real->bool) = {p | vec2 p IN convex hull (IMAGE vec2 V)}`;;

let PCONVEX_HULL_SUBSET = prove
 (`forall V. V SUBSET pconvex_hull V`,
  REWRITE_TAC[SUBSET; pconvex_hull; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
  REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* Mathlib: convexHull_min *)
let CO_PCONVEX_HULL_MIN = prove
 (`forall V S. V SUBSET S /\ pconvex S ==> pconvex_hull V SUBSET S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pconvex; pconvex_hull; SUBSET; IN_ELIM_THM] THEN
  STRIP_TAC THEN X_GEN_TAC `p:real#real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex hull (IMAGE vec2 V) SUBSET {x:real^2 | (x$1,x$2) IN S}` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; vec2; VECTOR_2] THEN
      ASM_REWRITE_TAC[PAIR];
      REWRITE_TAC[convex; IN_ELIM_THM; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`; `u:real`; `v:real`] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`(x:real^2)$1,(x:real^2)$2`; `(y:real^2)$1,(y:real^2)$2`;
        `u:real`; `v:real`] o check (fun th -> length(fst(strip_forall(concl th))) = 4)) THEN
      REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `vec2 p`) THEN ASM_REWRITE_TAC[vec2; VECTOR_2; PAIR]]);;

(* Lean: squareSet_convex *)
let CO_SQUARESET_CONVEX = prove
 (`forall c s u v a. pconvex (sqset c s u v a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pconvex; IN_SQSET] THEN
  MAP_EVERY X_GEN_TAC [`p:real#real`; `r:real#real`; `x:real`; `y:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `x = &1 - y` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CES_INSIDE_SEGMENT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: OverlapsAt *)
let overlaps_at = new_definition
 `overlaps_at (S1:real#real->bool) (S2:real#real->bool) A B <=>
    exists P. psub P A IN S1 /\ psub P B IN S2`;;

(* Lean: OverlapsAt.symm *)
let CO_OVERLAPSAT_SYMM = prove
 (`forall S1 S2 A B. overlaps_at S1 S2 A B <=> overlaps_at S2 S1 B A`,
  REWRITE_TAC[overlaps_at] THEN MESON_TAC[]);;

let CO_PCONVEX_TRANSLATE = prove
 (`forall S p r A0 A1 a b.
     pconvex S /\ psub p A0 IN S /\ psub r A1 IN S /\ &0 <= a /\ &0 <= b /\ a + b = &1
     ==> psub (a * FST p + b * FST r, a * SND p + b * SND r)
              (a * FST A0 + b * FST A1, a * SND A0 + b * SND A1) IN S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pconvex] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`psub p A0`; `psub r A1`; `a:real`; `b:real`]) THEN
  ASM_REWRITE_TAC[psub] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THEN REAL_ARITH_TAC);;

(* Lean: overlapsAt_convex_left *)
let CO_OVERLAPSAT_CONVEX_LEFT = prove
 (`forall c s u v a c' s' u' v' a' B.
     pconvex {A | overlaps_at (sqset c s u v a) (sqset c' s' u' v' a') A B}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pconvex; IN_ELIM_THM; overlaps_at] THEN
  MAP_EVERY X_GEN_TAC [`A0:real#real`; `A1:real#real`; `x:real`; `y:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `P0:real#real`)
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `P1:real#real`) STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(x * FST P0 + y * FST P1, x * SND P0 + y * SND P1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CO_PCONVEX_TRANSLATE THEN ASM_REWRITE_TAC[CO_SQUARESET_CONVEX];
    MP_TAC(SPECL [`sqset c' s' u' v' a'`; `P0:real#real`; `P1:real#real`;
                  `B:real#real`; `B:real#real`; `x:real`; `y:real`] CO_PCONVEX_TRANSLATE) THEN
    ASM_REWRITE_TAC[CO_SQUARESET_CONVEX] THEN
    SUBGOAL_THEN `(x * FST B + y * FST B, x * SND B + y * SND B) = B:real#real`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; ASSUME `x + y = &1`; REAL_MUL_LID; PAIR]]);;

(* Lean: overlapsAt_convex_right *)
let CO_OVERLAPSAT_CONVEX_RIGHT = prove
 (`forall c s u v a c' s' u' v' a' A.
     pconvex {B | overlaps_at (sqset c s u v a) (sqset c' s' u' v' a') A B}`,
  ONCE_REWRITE_TAC[CO_OVERLAPSAT_SYMM] THEN REWRITE_TAC[CO_OVERLAPSAT_CONVEX_LEFT]);;

(* Lean: vertex_overlap_extends *)
let CO_VERTEX_OVERLAP_EXTENDS = prove
 (`forall c s u v a c' s' u' v' a' VA VB.
     (forall A B. A IN VA /\ B IN VB ==> overlaps_at (sqset c s u v a) (sqset c' s' u' v' a') A B)
     ==> forall A B. A IN pconvex_hull VA /\ B IN pconvex_hull VB
               ==> overlaps_at (sqset c s u v a) (sqset c' s' u' v' a') A B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall A B. A IN pconvex_hull VA /\ B IN VB
     ==> overlaps_at (sqset c s u v a) (sqset c' s' u' v' a') A B` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`VA:real#real->bool`;
      `{A | overlaps_at (sqset c s u v a) (sqset c' s' u' v' a') A B}`] CO_PCONVEX_HULL_MIN) THEN
    REWRITE_TAC[CO_OVERLAPSAT_CONVEX_LEFT; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`VB:real#real->bool`;
      `{B | overlaps_at (sqset c s u v a) (sqset c' s' u' v' a') A B}`] CO_PCONVEX_HULL_MIN) THEN
    REWRITE_TAC[CO_OVERLAPSAT_CONVEX_RIGHT; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;
