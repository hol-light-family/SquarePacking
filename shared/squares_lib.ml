(* ========================================================================= *)
(* General lemmas about unit squares and packings.                           *)
(* ========================================================================= *)

needs "shared/squares_defs.ml";;

(* A square given by a corner p and an orthonormal frame u, w.               *)

let sqbox = new_definition
 `sqbox (p:real^2) (u:real^2) (w:real^2) =
    {x:real^2 | &0 <= (x - p) dot u /\ (x - p) dot u <= &1 /\
                &0 <= (x - p) dot w /\ (x - p) dot w <= &1}`;;

let ORTHONORMAL_2_EXPAND = prove
 (`forall u w y:real^2.
        u dot u = &1 /\ w dot w = &1 /\ u dot w = &0
        ==> y = (y dot u) % u + (y dot w) % w`,
  REWRITE_TAC[DOT_2; CART_EQ; DIMINDEX_2; FORALL_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

let UNIT_SQUARE_IMP_BOX = prove
 (`forall S:real^2->bool.
        unit_square S
        ==> exists p u w. u dot u = &1 /\ w dot w = &1 /\ u dot w = &0 /\
                    S = sqbox p u w`,
  GEN_TAC THEN REWRITE_TAC[unit_square] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `g = \x:real^2. f x - f(vec 0):real^2` THEN
  SUBGOAL_THEN `forall x:real^2. f x - f(vec 0) = (g:real^2->real^2) x`
  ASSUME_TAC THENL [EXPAND_TAC "g" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `orthogonal_transformation (g:real^2->real^2)` MP_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_ISOMETRY] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[VECTOR_SUB_REFL; dist;
                VECTOR_ARITH `(a - c) - (b - c):real^N = a - b`] THEN
    REWRITE_TAC[GSYM dist] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[orthogonal_transformation] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(f:real^2->real^2)(vec 0)`; `(g:real^2->real^2)(basis 1)`;
    `(g:real^2->real^2)(basis 2)`] THEN
  ASM_SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; sqbox; IN_ELIM_THM; IN_INTERVAL;
              DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
  X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH];
    STRIP_TAC THEN
    EXISTS_TAC `vector[(z - (f:real^2->real^2)(vec 0)) dot
                       (g:real^2->real^2)(basis 1);
                       (z - (f:real^2->real^2)(vec 0)) dot
                       (g:real^2->real^2)(basis 2)]:real^2` THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN
    SUBGOAL_THEN
     `z - (f:real^2->real^2)(vec 0) =
      (g:real^2->real^2)(vector[(z - f(vec 0)) dot g(basis 1);
                                (z - f(vec 0)) dot g(basis 2)])`
    MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM(ASSUME
        `forall x:real^2. f x - f(vec 0) = (g:real^2->real^2) x`)] THEN
      VECTOR_ARITH_TAC] THEN
    MP_TAC(ISPECL [`(g:real^2->real^2)(basis 1)`; `(g:real^2->real^2)(basis 2)`]
                  ORTHONORMAL_2_EXPAND) THEN
    ASM_SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH; VECTOR_2]]);;

let BOX_IMP_UNIT_SQUARE = prove
 (`forall p u w:real^2.
        u dot u = &1 /\ w dot w = &1 /\ u dot w = &0
        ==> unit_square(sqbox p u w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[unit_square] THEN
  EXISTS_TAC `\x:real^2. p + x$1 % u + x$2 % w:real^2` THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[DIST_EQ; dist; NORM_POW_2] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DOT_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VECTOR_SUB_COMPONENT] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; sqbox; IN_ELIM_THM; IN_INTERVAL;
              DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
  X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    EXISTS_TAC `vector[(z - p:real^2) dot u; (z - p:real^2) dot w]:real^2` THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN
    MP_TAC(ISPECL [`u:real^2`; `w:real^2`; `z - p:real^2`]
                  ORTHONORMAL_2_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(p + a % u + b % w) - p:real^N = a % u + b % w`;
                    DOT_LADD; DOT_LMUL] THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let UNIT_SQUARE_BOX = prove
 (`forall S:real^2->bool.
        unit_square S <=>
        exists p u w. u dot u = &1 /\ w dot w = &1 /\ u dot w = &0 /\
                S = sqbox p u w`,
  MESON_TAC[UNIT_SQUARE_IMP_BOX; BOX_IMP_UNIT_SQUARE]);;

(* In the plane, an orthonormal pair is a rotation or a reflection frame.    *)

let W_CASES = prove
 (`forall u1 u2 w1 w2.
        u1 * u1 + u2 * u2 = &1 /\ w1 * w1 + w2 * w2 = &1 /\
        u1 * w1 + u2 * w2 = &0
        ==> (w1 = --u2 /\ w2 = u1) \/ (w1 = u2 /\ w2 = --u1)`,
  CONV_TAC REAL_RING);;

(* Strict inequalities give interior points.                                 *)

let IN_INTERIOR_SQBOX = prove
 (`forall p u w z:real^2.
        &0 < (z - p) dot u /\ (z - p) dot u < &1 /\
        &0 < (z - p) dot w /\ (z - p) dot w < &1
        ==> z IN interior(sqbox p u w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x:real^2 | &0 < (x - p) dot u /\ (x - p) dot u < &1 /\
                &0 < (x - p) dot w /\ (x - p) dot w < &1}
    SUBSET interior(sqbox p u w)`
  MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[sqbox; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{x:real^2 | &0 < (x - p) dot u /\ (x - p) dot u < &1 /\
                  &0 < (x - p) dot w /\ (x - p) dot w < &1} =
      {x | u dot x > u dot p} INTER {x | u dot x < &1 + u dot p} INTER
      {x | w dot x > w dot p} INTER {x | w dot x < &1 + w dot p}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_LSUB] THEN
      REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* Separation of interiors by a line.                                        *)

let DISJOINT_INTERIORS_SEPARATED = prove
 (`forall a b s t:real^2->bool.
        ~(a = vec 0) /\
        (forall x. x IN s ==> a dot x <= b) /\ (forall x. x IN t ==> b <= a dot x)
        ==> DISJOINT (interior s) (interior t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `interior s SUBSET {x:real^2 | a dot x < b} /\
                interior t SUBSET {x:real^2 | --a dot x < --b}`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM INTERIOR_HALFSPACE_LE] THEN
    MP_TAC(ISPECL [`--a:real^2`; `--b:real`] INTERIOR_HALFSPACE_LE) THEN
    ASM_REWRITE_TAC[VECTOR_NEG_EQ_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; DOT_LNEG] THEN
    ASM_MESON_TAC[REAL_LE_NEG2];
    REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                IN_ELIM_THM; DOT_LNEG] THEN
    MESON_TAC[REAL_LT_NEG2; REAL_LT_ANTISYM]]);;

(* Monotonicity of packability in the container side.                        *)

let PACKS_MONO = prove
 (`forall n t t'. packs n t /\ t <= t' ==> packs n t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[packs] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> u SUBSET s ==> u SUBSET t`) THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VEC_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;

(* Corners of a square inside the container.                                 *)

let SQBOX_CORNERS = prove
 (`forall p u w:real^2.
        u dot u = &1 /\ w dot w = &1 /\ u dot w = &0
        ==> p IN sqbox p u w /\ p + u IN sqbox p u w /\
            p + w IN sqbox p u w /\ p + u + w IN sqbox p u w`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sqbox; IN_ELIM_THM;
              VECTOR_ARITH `(p + u) - p:real^N = u /\ (p + u + w) - p = u + w /\
                            p - p = vec 0`] THEN
  REWRITE_TAC[DOT_LADD; DOT_LZERO] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let IN_CONTAINER = prove
 (`forall x:real^2 t. x IN interval[vec 0,t % vec 1] <=>
                &0 <= x$1 /\ x$1 <= t /\ &0 <= x$2 /\ x$2 <= t`,
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT;
              VECTOR_MUL_COMPONENT; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

(* A product bound.                                                          *)

let BILIN = prove
 (`forall p x l h. &0 <= p /\ l <= x /\ x <= h ==> p * l <= p * x /\ p * x <= p * h`,
  SIMP_TAC[REAL_LE_LMUL]);;

let SQ_LE_IMP_LIB = prove
 (`forall x y. &0 <= y /\ x * x <= y * y ==> x <= y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= abs y /\ &0 <= y ==> x <= y`) THEN
  ASM_REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC);;

(* Pigeonhole.                                                               *)

let PIGEONHOLE_POINTS = prove
 (`forall n z:num->A s.
        FINITE s /\ CARD s < n /\ (forall i. i < n ==> z i IN s)
        ==> exists i j. i < n /\ j < n /\ ~(i = j) /\ z i = z j`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z:num->A`; `{i:num | i < n}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (z:num->A) {i | i < n}`; `s:A->bool`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[CARD_NUMSEG_LT] THEN ASM_ARITH_TAC);;
