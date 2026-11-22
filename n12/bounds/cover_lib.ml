(* ========================================================================= *)
(* Weighted point covers and lower bounds for square packing.                *)
(*                                                                           *)
(* If every closed unit square inside [0,m]^2 contains points of total       *)
(* weight >= 1 from a finite weighted point family of total weight < n,      *)
(* then n unit squares do not pack into a square of any side t < m.          *)
(* ========================================================================= *)

needs "shared/squares_lib.ml";;

(* ------------------------------------------------------------------------- *)
(* Captured weight.                                                          *)
(* ------------------------------------------------------------------------- *)

let capt = new_definition
 `capt (pts:num->real^2) (wt:num->real) N (S:real^2->bool) =
    sum {k | k < N} (\k. if pts k IN S then wt k else &0)`;;

let SUM_CAPT_LE = prove
 (`forall pts:num->real^2 wt N n (U:num->real^2->bool).
        (forall k. k < N ==> &0 <= wt k) /\
        (forall i j. i < n /\ j < n /\ ~(i:num = j) ==> DISJOINT (U i) (U j))
        ==> sum {i | i < n} (\i. capt pts wt N (U i)) <= sum {k | k < N} wt`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[capt] THEN
  MP_TAC(ISPECL [`\i k. if (pts:num->real^2) k IN (U:num->real^2->bool) i then (wt:num->real) k
                       else &0`; `{i:num | i < n}`; `{k:num | k < N}`] SUM_SWAP) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `exists i. i < n /\ (pts:num->real^2) k IN (U:num->real^2->bool) i` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i0:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {i | i < n} (\i. if i = (i0:num) then (wt:num->real) k else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `i:num = i0` THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `i0:num`]) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[SUM_DELTA; IN_ELIM_THM]];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum {i | i < n} (\i:num. &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[SUM_0]]]);;

(* ------------------------------------------------------------------------- *)
(* Unit squares by centre and direction.                                     *)
(* ------------------------------------------------------------------------- *)

let rsq = new_definition
 `rsq c1 c2 a b =
    {z:real^2 | abs((z$1 - c1) * a + (z$2 - c2) * b) <= &1 / &2 /\
                abs((z$2 - c2) * a - (z$1 - c1) * b) <= &1 / &2}`;;

let RSQ_ROT = prove
 (`forall c1 c2 a b. rsq c1 c2 (--b) a = rsq c1 c2 a b`,
  REWRITE_TAC[rsq; EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let RSQ_NEG = prove
 (`forall c1 c2 a b. rsq c1 c2 (--a) (--b) = rsq c1 c2 a b`,
  REWRITE_TAC[rsq; EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let SQBOX_RSQ = prove
 (`forall p u w:real^2.
        u dot u = &1 /\ w dot w = &1 /\ u dot w = &0
        ==> sqbox p u w = rsq (p$1 + (u$1 + w$1) / &2) (p$2 + (u$2 + w$2) / &2)
                              (u$1) (u$2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DOT_2] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(u:real^2)$1`; `(u:real^2)$2`; `(w:real^2)$1`; `(w:real^2)$2`]
               W_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[sqbox; rsq; EXTENSION; IN_ELIM_THM; DOT_2; VECTOR_SUB_COMPONENT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN
  UNDISCH_TAC `(u:real^2)$1 * (u:real^2)$1 + (u:real^2)$2 * (u:real^2)$2 = &1` THEN
  REAL_ARITH_TAC);;

(* Normal form of a unit square in the container [0,m]^2.                   *)

let UNIT_SQUARE_NORMAL = prove
 (`forall S m. unit_square S /\ S SUBSET interval[vec 0,m % vec 1]
         ==> exists c1 c2 a b. &0 <= a /\ &0 <= b /\ a * a + b * b = &1 /\
                         S = rsq c1 c2 a b /\
                         (a + b) / &2 <= c1 /\ c1 <= m - (a + b) / &2 /\
                         (a + b) / &2 <= c2 /\ c2 <= m - (a + b) / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIT_SQUARE_BOX] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `u:real^2`
     (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC))) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:real^2`; `u:real^2`; `w:real^2`] SQBOX_CORNERS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `forall x:real^2. x IN sqbox p u w ==> &0 <= x$1 /\ x$1 <= m /\ &0 <= x$2 /\ x$2 <= m`
  MP_TAC THENL
   [REWRITE_TAC[GSYM IN_CONTAINER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MAP_EVERY (fun t -> MP_TAC(MATCH_MP th (ASSUME t)))
     [`p IN sqbox p u w`; `p + u IN sqbox p u w`;
      `p + w IN sqbox p u w`; `p + u + w IN sqbox p u w`]) THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SQBOX_RSQ] THEN
  UNDISCH_TAC `(u:real^2) dot u = &1` THEN
  UNDISCH_TAC `(w:real^2) dot w = &1` THEN
  UNDISCH_TAC `(u:real^2) dot w = &0` THEN REWRITE_TAC[DOT_2] THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(p:real^2)$1 + ((u:real^2)$1 + (w:real^2)$1) / &2`;
    `(p:real^2)$2 + ((u:real^2)$2 + (w:real^2)$2) / &2`] THEN
  MP_TAC(SPECL [`(u:real^2)$1`; `(u:real^2)$2`; `(w:real^2)$1`; `(w:real^2)$2`]
               W_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  (ASM_CASES_TAC `&0 <= (u:real^2)$1` THEN ASM_CASES_TAC `&0 <= (u:real^2)$2` THENL
   [MAP_EVERY EXISTS_TAC [`(u:real^2)$1`; `(u:real^2)$2`];
    MAP_EVERY EXISTS_TAC [`--((u:real^2)$2)`; `(u:real^2)$1`];
    MAP_EVERY EXISTS_TAC [`(u:real^2)$2`; `--((u:real^2)$1)`];
    MAP_EVERY EXISTS_TAC [`--((u:real^2)$1)`; `--((u:real^2)$2)`]] THEN
   REPEAT CONJ_TAC THEN
   TRY(REWRITE_TAC[rsq; EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC THEN NO_TAC) THEN
   ASM_REAL_ARITH_TAC));;

(* ------------------------------------------------------------------------- *)
(* The cover argument.                                                       *)
(* ------------------------------------------------------------------------- *)

let SCALE_IN_INTERIOR = prove
 (`forall p u w l z:real^2.
        u dot u = &1 /\ w dot w = &1 /\ u dot w = &0 /\ &1 < l /\
        z IN sqbox (l % (p + inv(&2) % (u + w)) - inv(&2) % (u + w)) u w
        ==> inv l % z IN interior(sqbox p u w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC IN_INTERIOR_SQBOX THEN
  SUBGOAL_THEN `w dot (u:real^2) = &0` ASSUME_TAC THENL
   [ASM_MESON_TAC[DOT_SYM]; ALL_TAC] THEN
  UNDISCH_TAC `z IN sqbox (l % (p + inv(&2) % (u + w)) - inv(&2) % (u + w)) u w` THEN
  REWRITE_TAC[sqbox; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[DOT_LSUB; DOT_LMUL; DOT_LADD] THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `forall A B. inv l * A - B = (A - l * B) / l`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REPEAT GEN_TAC THEN UNDISCH_TAC `&0 < l` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_MUL_LZERO; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `inv(&2) * (&1 + &0) = &1 / &2 /\
                          inv(&2) * (&0 + &1) = &1 / &2`] THEN
  ASM_REAL_ARITH_TAC);;

let UNIT_SQUARE_IN_CONTAINER_POS = prove
 (`forall S t. unit_square S /\ S SUBSET interval[vec 0,t % vec 1] ==> &0 < t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIT_SQUARE_BOX] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `u:real^2`
     (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC))) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:real^2`; `u:real^2`; `w:real^2`] SQBOX_CORNERS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^2) IN interval[vec 0,t % vec 1] /\
                p + u IN interval[vec 0,t % vec 1]` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_CONTAINER; VECTOR_ADD_COMPONENT] THEN
  UNDISCH_TAC `(u:real^2) dot u = &1` THEN REWRITE_TAC[DOT_2] THEN
  ASM_CASES_TAC `&0 < t` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2)$1 = &0 /\ (u:real^2)$2 = &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(u:real^2)$1 * (u:real^2)$1 + (u:real^2)$2 * (u:real^2)$2 = &1` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SCALE_CONTAINER = prove
 (`forall l t m z:real^2. &1 < l /\ l * t = m /\ inv l % z IN interval[vec 0,t % vec 1]
        ==> z IN interval[vec 0,m % vec 1]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_CONTAINER; VECTOR_MUL_COMPONENT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^2)$1 = l * (inv l * z$1) /\ (z:real^2)$2 = l * (inv l * z$2)`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `&1 < l` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun tm -> MP_TAC(SPECL [`l:real`; tm; `&0`; `t:real`] BILIN))
      [`inv l * (z:real^2)$1`; `inv l * (z:real^2)$2`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let has_const name tm =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) tm;;

let COVER_NO_PACK = prove
 (`forall n N (pts:num->real^2) wt m t.
        (forall k. k < N ==> &0 <= wt k) /\ sum {k | k < N} wt < &n /\
        (forall S. unit_square S /\ S SUBSET interval[vec 0,m % vec 1]
             ==> &1 <= capt pts wt N S) /\
        t < m
        ==> ~packs n t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[packs; NOT_EXISTS_THM] THEN
  X_GEN_TAC `sq:num->real^2->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_TAC `sum {k | k < N} (wt:num->real) < &n` THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [MATCH_MP_TAC UNIT_SQUARE_IN_CONTAINER_POS THEN
    EXISTS_TAC `(sq:num->real^2->bool) 0` THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `l = m / t` THEN
  SUBGOAL_THEN `&1 < l /\ l * t = m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_DIV_RMUL;
                                     REAL_LT_IMP_NZ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `forall i. exists p u w. i < n ==> u dot u = &1 /\ w dot w = &1 /\ u dot w = &0 /\
                          (sq:num->real^2->bool) i = sqbox p u w`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM UNIT_SQUARE_BOX] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real^2` (X_CHOOSE_THEN `u:num->real^2`
    (X_CHOOSE_TAC `w:num->real^2`))) THEN
  ABBREV_TAC
   `U = \i. sqbox (l % ((p:num->real^2) i + inv(&2) % (u i + w i)) -
                   inv(&2) % (u i + w i)) (u i) (w i)` THEN
  SUBGOAL_THEN
   `forall i z. i < n /\ z IN (U:num->real^2->bool) i
          ==> inv l % z IN interior((sq:num->real^2->bool) i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[ASSUME `i:num < n`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCALE_IN_INTERIOR THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `z IN (U:num->real^2->bool) i` THEN EXPAND_TAC "U" THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {i | i < n} (\i. capt pts wt N ((U:num->real^2->bool) i)) <
    sum {i | i < n} (\i. &1)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum {k | k < N} (wt:num->real)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_CAPT_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER;
                                        NOT_IN_EMPTY] THEN
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o
        check (fun th -> is_forall(concl th) && has_const "DISJOINT" (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `inv l % z:real^2`) THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT;
                   REAL_MUL_RID]];
    REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> has_const "capt" (concl th))) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "U" THEN REWRITE_TAC[] THEN MATCH_MP_TAC BOX_IMP_UNIT_SQUARE THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC SCALE_CONTAINER THEN
    MAP_EVERY EXISTS_TAC [`l:real`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `interior((sq:num->real^2->bool) i) SUBSET
                  interval[vec 0,t % vec 1]` MP_TAC THENL
     [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Symmetry reduction (the dihedral group of the container).                 *)
(* ------------------------------------------------------------------------- *)

let CAPT_PERM = prove
 (`forall pts:num->real^2 wt N S S' p.
        (forall k. k < N ==> p k < N /\ p(p k) = k /\ wt(p k) = wt k /\
                       (pts(p k) IN S' <=> pts k IN S))
        ==> capt pts wt N S' = capt pts wt N S`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[capt] THEN
  MP_TAC(ISPECL [`\k. if (pts:num->real^2) k IN S' then (wt:num->real) k else &0`;
                 `p:num->num`; `{k:num | k < N}`] SUM_BIJECTION) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ASM_SIMP_TAC[]);;

let d4inv = new_definition
 `d4inv (pts:num->real^2) (wt:num->real) N m px py ps <=>
    forall k. k < N ==>
        px k < N /\ px(px k) = k /\ wt(px k) = wt k /\
        pts(px k) = vector[m - pts k$1; pts k$2] /\
        py k < N /\ py(py k) = k /\ wt(py k) = wt k /\
        pts(py k) = vector[pts k$1; m - pts k$2] /\
        ps k < N /\ ps(ps k) = k /\ wt(ps k) = wt k /\
        pts(ps k) = vector[pts k$2; pts k$1]`;;

let adm = new_definition
 `adm m c1 c2 a b <=>
    &0 <= a /\ &0 <= b /\ a * a + b * b = &1 /\
    (a + b) / &2 <= c1 /\ c1 <= m - (a + b) / &2 /\
    (a + b) / &2 <= c2 /\ c2 <= m - (a + b) / &2`;;

let D4_CAPT = prove
 (`forall pts:num->real^2 wt N m px py ps c1 c2 a b.
        d4inv pts wt N m px py ps
        ==> capt pts wt N (rsq (m - c1) c2 b a) = capt pts wt N (rsq c1 c2 a b) /\
            capt pts wt N (rsq c1 (m - c2) b a) = capt pts wt N (rsq c1 c2 a b) /\
            capt pts wt N (rsq c2 c1 b a) = capt pts wt N (rsq c1 c2 a b)`,
  REWRITE_TAC[d4inv] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CAPT_PERM THENL
   [EXISTS_TAC `px:num->num`; EXISTS_TAC `py:num->num`;
    EXISTS_TAC `ps:num->num`] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[rsq; IN_ELIM_THM; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let D4_REDUCE = prove
 (`forall pts:num->real^2 wt N m px py ps.
        d4inv pts wt N m px py ps /\
        (forall c1 c2 a b. adm m c1 c2 a b /\ c1 <= m / &2 /\ c2 <= m / &2 /\ b <= a
                     ==> &1 <= capt pts wt N (rsq c1 c2 a b))
        ==> forall c1 c2 a b. adm m c1 c2 a b ==> &1 <= capt pts wt N (rsq c1 c2 a b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP D4_CAPT) ASSUME_TAC) THEN
  SUBGOAL_THEN
   `forall c1 c2 a b. adm m c1 c2 a b /\ c1 <= m / &2 /\ c2 <= m / &2
                ==> &1 <= capt pts wt N (rsq c1 c2 a b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `b <= a:real` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2
      (SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`] th)))]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `adm m c1 c2 a b` THEN REWRITE_TAC[adm] THEN
    UNDISCH_TAC `~(b <= a:real)` THEN UNDISCH_TAC `c1 <= m / &2` THEN
    UNDISCH_TAC `c2 <= m / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `forall c1 c2 a b. adm m c1 c2 a b /\ c1 <= m / &2
                ==> &1 <= capt pts wt N (rsq c1 c2 a b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `c2 <= m / &2` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2
      (SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`] th)))]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `adm m c1 c2 a b` THEN REWRITE_TAC[adm] THEN
    UNDISCH_TAC `~(c2 <= m / &2)` THEN UNDISCH_TAC `c1 <= m / &2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c1 <= m / &2` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(CONJUNCT1
    (SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`] th))]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `adm m c1 c2 a b` THEN REWRITE_TAC[adm] THEN
  UNDISCH_TAC `~(c1 <= m / &2)` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tangent half-angle parametrisation.                                   *)
(* ------------------------------------------------------------------------- *)

let tsq = new_definition
 `tsq c1 c2 t =
    {z:real^2 | abs((z$1 - c1) * (&1 - t * t) + (z$2 - c2) * (&2 * t))
                <= (&1 + t * t) / &2 /\
                abs((z$2 - c2) * (&1 - t * t) - (z$1 - c1) * (&2 * t))
                <= (&1 + t * t) / &2}`;;

let wall = new_definition
 `wall t = (&1 - t * t + &2 * t) / (&2 * (&1 + t * t))`;;

let T_PARAM = prove
 (`forall a b. &0 <= b /\ b <= a /\ a * a + b * b = &1
         ==> exists t. &0 <= t /\ t <= &29 / &70 /\
                 (forall c1 c2. rsq c1 c2 a b = tsq c1 c2 t) /\
                 (a + b) / &2 = wall t`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `b / (&1 + a)` THEN
  SUBGOAL_THEN `&0 < &1 + a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = b / (&1 + a)` THEN
  SUBGOAL_THEN `&1 - t * t = a * (&1 + t * t) /\ &2 * t = b * (&1 + t * t)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    UNDISCH_TAC `a * a + b * b = &1` THEN UNDISCH_TAC `&0 < &1 + a` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + t * t` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&4059 <= &5741 * a` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(&5741 * a < &4059) ==> &4059 <= &5741 * a`) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `a * a < (&4059 / &5741) * (&4059 / &5741)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPECL [`b:real`; `a:real`; `b:real`; `a:real`] REAL_LE_MUL2) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&70 * b <= &29 * (&1 + a) ==> b <= &29 / &70 * (&1 + a)`) THEN
    MATCH_MP_TAC SQ_LE_IMP_LIB THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&1 + a`; `&5741 * a - &4059`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[rsq; tsq; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `x * a * k + y * b * k = k * (x * a + y * b) /\
                            y * a * k - x * b * k = k * (y * a - x * b)`] THEN
    ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < k ==> abs k = k`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> (k * x <= k / &2 <=> k * x <= k * (&1 / &2))`;
                 REAL_LE_LMUL_EQ];
    REWRITE_TAC[wall] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < &1 + t * t` THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Root cover statement => cover of all unit squares.                        *)
(* ------------------------------------------------------------------------- *)

let TCOVER_IMP_COVER = prove
 (`forall pts:num->real^2 wt N m px py ps.
        d4inv pts wt N m px py ps /\
        (forall c1 c2 t. &0 <= t /\ t <= &29 / &70 /\ c1 <= m / &2 /\ c2 <= m / &2 /\
                   wall t <= c1 /\ c1 <= m - wall t /\
                   wall t <= c2 /\ c2 <= m - wall t
                   ==> &1 <= capt pts wt N (tsq c1 c2 t))
        ==> forall S. unit_square S /\ S SUBSET interval[vec 0,m % vec 1]
                ==> &1 <= capt pts wt N S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `S:real^2->bool` THEN
  DISCH_THEN(MP_TAC o MATCH_MP UNIT_SQUARE_NORMAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `c2:real`; `a:real`; `b:real`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`pts:num->real^2`; `wt:num->real`; `N:num`; `m:real`;
                 `px:num->num`; `py:num->num`; `ps:num->num`] D4_REDUCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[adm] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a':real`; `b':real`] T_PARAM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[adm]]);;

(* ------------------------------------------------------------------------- *)
(* Box covers on an integer grid: the statement checked leaf by leaf.        *)
(* ------------------------------------------------------------------------- *)

let boxcov = new_definition
 `boxcov (pts:num->real^2) wt N m Q R x0 x1 y0 y1 u0 u1 <=>
    forall c1 c2 t. &x0 / &Q <= c1 /\ c1 <= &x1 / &Q /\
              &y0 / &Q <= c2 /\ c2 <= &y1 / &Q /\
              &u0 / &R <= t /\ t <= &u1 / &R /\
              wall t <= c1 /\ c1 <= m - wall t /\
              wall t <= c2 /\ c2 <= m - wall t
              ==> &1 <= capt pts wt N (tsq c1 c2 t)`;;

let BOXCOV_SPLIT_X = prove
 (`forall pts:num->real^2 wt N m Q R x0 x1 xm y0 y1 u0 u1.
        boxcov pts wt N m Q R x0 xm y0 y1 u0 u1 /\
        boxcov pts wt N m Q R xm x1 y0 y1 u0 u1
        ==> boxcov pts wt N m Q R x0 x1 y0 y1 u0 u1`,
  REWRITE_TAC[boxcov] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c1 <= &xm / &Q` THEN ASM_MESON_TAC[REAL_LE_TOTAL]);;

let BOXCOV_SPLIT_Y = prove
 (`forall pts:num->real^2 wt N m Q R x0 x1 y0 y1 ym u0 u1.
        boxcov pts wt N m Q R x0 x1 y0 ym u0 u1 /\
        boxcov pts wt N m Q R x0 x1 ym y1 u0 u1
        ==> boxcov pts wt N m Q R x0 x1 y0 y1 u0 u1`,
  REWRITE_TAC[boxcov] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c2 <= &ym / &Q` THEN ASM_MESON_TAC[REAL_LE_TOTAL]);;

let BOXCOV_SPLIT_U = prove
 (`forall pts:num->real^2 wt N m Q R x0 x1 y0 y1 u0 u1 um.
        boxcov pts wt N m Q R x0 x1 y0 y1 u0 um /\
        boxcov pts wt N m Q R x0 x1 y0 y1 um u1
        ==> boxcov pts wt N m Q R x0 x1 y0 y1 u0 u1`,
  REWRITE_TAC[boxcov] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t <= &um / &R` THEN ASM_MESON_TAC[REAL_LE_TOTAL]);;

let BOXCOV_ROOT = prove
 (`forall pts:num->real^2 wt N m Q R px py ps X1 Y1 U1.
        d4inv pts wt N m px py ps /\ 0 < Q /\ 0 < R /\
        m / &2 <= &X1 / &Q /\ m / &2 <= &Y1 / &Q /\ &29 / &70 <= &U1 / &R /\
        boxcov pts wt N m Q R 0 X1 0 Y1 0 U1
        ==> forall S. unit_square S /\ S SUBSET interval[vec 0,m % vec 1]
                ==> &1 <= capt pts wt N S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[boxcov] THEN STRIP_TAC THEN
  MATCH_MP_TAC TCOVER_IMP_COVER THEN
  MAP_EVERY EXISTS_TAC [`px:num->num`; `py:num->num`; `ps:num->num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `&0 <= wall t` MP_TAC THENL
   [REWRITE_TAC[wall] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN
    MP_TAC(SPECL [`t:real`; `&29 / &70`; `t:real`; `&29 / &70`] REAL_LE_MUL2) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Leaf test: a point lies in every square of a pose box.                    *)
(* ------------------------------------------------------------------------- *)

let BERN2 = prove
 (`forall a b c t0 t1 t.
        t0 <= t /\ t <= t1 /\
        a * t0 * t0 + b * t0 + c <= &0 /\
        a * t1 * t1 + b * t1 + c <= &0 /\
        a * t0 * t1 + b * (t0 + t1) / &2 + c <= &0
        ==> a * t * t + b * t + c <= &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t0:real = t1` THENL
   [SUBGOAL_THEN `t:real = t0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (t1 - t0) * (t1 - t0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`(t1 - t) * (t1 - t)`; `--(a * t0 * t0 + b * t0 + c)`]
               REAL_LE_MUL) THEN
  MP_TAC(SPECL [`(t - t0) * (t1 - t)`;
                `--(a * t0 * t1 + b * (t0 + t1) / &2 + c)`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`(t - t0) * (t - t0)`; `--(a * t1 * t1 + b * t1 + c)`]
               REAL_LE_MUL) THEN
  MP_TAC(SPECL [`t - t0`; `t1 - t`] REAL_LE_MUL) THEN
  REWRITE_TAC[REAL_LE_SQUARE] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < x) ==> x <= &0`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`(t1 - t0) * (t1 - t0)`; `a * t * t + b * t + c`] REAL_LT_MUL) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let kcond = new_definition
 `kcond s0 s1 p q <=>
    &2 * (&1 - s0 * s1) * p + &2 * (s0 + s1) * q <= &1 + s0 * s1`;;

let KCOND_INTERVAL = prove
 (`forall t0 t1 p q.
        kcond t0 t0 p q /\ kcond t1 t1 p q /\ kcond t0 t1 p q
        ==> forall t. t0 <= t /\ t <= t1 ==> kcond t t p q`,
  REWRITE_TAC[kcond] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`--(&2 * p) - &1`; `&4 * q`; `&2 * p - &1`;
                `t0:real`; `t1:real`; `t:real`] BERN2) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let PT_REAL = prove
 (`forall t0 t1 xl xh yl yh zx zy.
        &0 <= t0 /\ t0 <= t1 /\ t1 <= &1 /\
        kcond t0 t0 (zx - xl) (zy - yl) /\ kcond t1 t1 (zx - xl) (zy - yl) /\
        kcond t0 t1 (zx - xl) (zy - yl) /\
        kcond t0 t0 (xh - zx) (yh - zy) /\ kcond t1 t1 (xh - zx) (yh - zy) /\
        kcond t0 t1 (xh - zx) (yh - zy) /\
        kcond t0 t0 (zy - yl) (xh - zx) /\ kcond t1 t1 (zy - yl) (xh - zx) /\
        kcond t0 t1 (zy - yl) (xh - zx) /\
        kcond t0 t0 (yh - zy) (zx - xl) /\ kcond t1 t1 (yh - zy) (zx - xl) /\
        kcond t0 t1 (yh - zy) (zx - xl)
        ==> forall c1 c2 t. xl <= c1 /\ c1 <= xh /\ yl <= c2 /\ c2 <= yh /\
                      t0 <= t /\ t <= t1
                      ==> vector[zx; zy] IN tsq c1 c2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (p,q) ->
    MP_TAC(SPECL [`t0:real`; `t1:real`; p; q] KCOND_INTERVAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[kcond] THEN DISCH_TAC)
   [`zx - xl:real`, `zy - yl:real`; `xh - zx:real`, `yh - zy:real`;
    `zy - yl:real`, `xh - zx:real`; `yh - zy:real`, `zx - xl:real`] THEN
  SUBGOAL_THEN `&0 <= &1 - t * t /\ &0 <= t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MP_TAC(SPECL [`t:real`; `&1`; `t:real`; `&1`] REAL_LE_MUL2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1 - t * t`; `c1:real`; `xl:real`; `xh:real`] BILIN) THEN
  MP_TAC(SPECL [`&1 - t * t`; `c2:real`; `yl:real`; `yh:real`] BILIN) THEN
  MP_TAC(SPECL [`t:real`; `c1:real`; `xl:real`; `xh:real`] BILIN) THEN
  MP_TAC(SPECL [`t:real`; `c2:real`; `yl:real`; `yh:real`] BILIN) THEN
  ASM_REWRITE_TAC[tsq; IN_ELIM_THM; VECTOR_2] THEN ASM_REAL_ARITH_TAC);;

let NAT_KCOND = prove
 (`forall Q R s0 s1 X Y p q a b g.
        0 < Q /\ 0 < R /\ s0 * s1 <= R * R /\
        a = 2 * (R * R - s0 * s1) /\ b = 2 * R * (s0 + s1) /\ g = R * R + s0 * s1 /\
        a * X + b * Y <= g * Q + a * p + b * q
        ==> kcond (&s0 / &R) (&s1 / &R) ((&X - &p) / &Q) ((&Y - &q) / &Q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[kcond] THEN
  SUBGOAL_THEN `&0 < &Q /\ &0 < &R` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  ABBREV_TAC `QQ = &Q` THEN ABBREV_TAC `RR = &R` THEN
  SUBGOAL_THEN `&0 < RR * RR * QQ` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  DISCH_TAC THEN
  W(fun (asl,w) ->
    let x,y = dest_binary "real_le" w in
    let k = `RR * RR * QQ` in
    MP_TAC(SPECL [x; y] (MATCH_MP REAL_LE_LMUL_EQ (ASSUME `&0 < RR * RR * QQ`))) THEN
    SUBGOAL_THEN (mk_conj(mk_eq(mk_binary "real_mul" (k,x),
       `&2 * (RR * RR - &s0 * &s1) * (&X - &p) + &2 * RR * (&s0 + &s1) * (&Y - &q)`),
                          mk_eq(mk_binary "real_mul" (k,y),
       `(RR * RR + &s0 * &s1) * QQ`)))
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN UNDISCH_TAC `&0 < QQ` THEN UNDISCH_TAC `&0 < RR` THEN
      CONV_TAC REAL_FIELD;
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC]));;

let PT_NAT = prove
 (`forall Q R u0 u1 xl xh yl yh X Y a0 b0 g0 a1 b1 g1 a2 b2 g2.
        0 < Q /\ 0 < R /\ u0 <= u1 /\ u1 <= R /\
        a0 = 2 * (R * R - u0 * u0) /\ b0 = 2 * R * (u0 + u0) /\ g0 = R * R + u0 * u0 /\
        a1 = 2 * (R * R - u1 * u1) /\ b1 = 2 * R * (u1 + u1) /\ g1 = R * R + u1 * u1 /\
        a2 = 2 * (R * R - u0 * u1) /\ b2 = 2 * R * (u0 + u1) /\ g2 = R * R + u0 * u1 /\
        a0 * X + b0 * Y <= g0 * Q + a0 * xl + b0 * yl /\
        a0 * xh + b0 * yh <= g0 * Q + a0 * X + b0 * Y /\
        a0 * Y + b0 * xh <= g0 * Q + a0 * yl + b0 * X /\
        a0 * yh + b0 * X <= g0 * Q + a0 * Y + b0 * xl /\
        a1 * X + b1 * Y <= g1 * Q + a1 * xl + b1 * yl /\
        a1 * xh + b1 * yh <= g1 * Q + a1 * X + b1 * Y /\
        a1 * Y + b1 * xh <= g1 * Q + a1 * yl + b1 * X /\
        a1 * yh + b1 * X <= g1 * Q + a1 * Y + b1 * xl /\
        a2 * X + b2 * Y <= g2 * Q + a2 * xl + b2 * yl /\
        a2 * xh + b2 * yh <= g2 * Q + a2 * X + b2 * Y /\
        a2 * Y + b2 * xh <= g2 * Q + a2 * yl + b2 * X /\
        a2 * yh + b2 * X <= g2 * Q + a2 * Y + b2 * xl
        ==> forall c1 c2 t. &xl / &Q <= c1 /\ c1 <= &xh / &Q /\
                      &yl / &Q <= c2 /\ c2 <= &yh / &Q /\
                      &u0 / &R <= t /\ t <= &u1 / &R
                      ==> vector[&X / &Q; &Y / &Q] IN tsq c1 c2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&u0 / &R`; `&u1 / &R`; `&xl / &Q`; `&xh / &Q`; `&yl / &Q`;
                `&yh / &Q`; `&X / &Q`; `&Y / &Q`] PT_REAL) THEN
  MATCH_MP_TAC(TAUT `a ==> (a ==> b) ==> b`) THEN
  SUBGOAL_THEN `&0 < &R` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(u0:num) * u0 <= R * R /\ (u1:num) * u1 <= R * R /\ (u0:num) * u1 <= R * R`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a / q - b / q = (a - b) / q`] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC NAT_KCOND THEN
  ASM_REWRITE_TAC[] THEN
  FIRST [EXISTS_TAC `a0:num` THEN EXISTS_TAC `b0:num` THEN EXISTS_TAC `g0:num` THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         EXISTS_TAC `a1:num` THEN EXISTS_TAC `b1:num` THEN EXISTS_TAC `g1:num` THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         EXISTS_TAC `a2:num` THEN EXISTS_TAC `b2:num` THEN EXISTS_TAC `g2:num` THEN
         ASM_REWRITE_TAC[] THEN NO_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Walls: a lower bound for the half-width (cos t + sin t)/2 on a bin.       *)
(* ------------------------------------------------------------------------- *)

let WALL_LB = prove
 (`forall Q R u0 u1 WL t.
        0 < Q /\ 0 < R /\ u0 <= u1 /\ u1 <= R /\
        WL * (2 * (R * R + u1 * u1)) <= Q * ((R * R + 2 * u0 * R) - u1 * u1) /\
        &u0 / &R <= t /\ t <= &u1 / &R
        ==> &WL / &Q <= wall t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &Q /\ &0 < &R` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t /\ t <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&u0 / &R` THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&u1 / &R` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * (&1 + t * t)` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[wall] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `a / b * c = (a * c) / b`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ASM_CASES_TAC `(R:num) * R + 2 * u0 * R <= u1 * u1` THENL
   [SUBGOAL_THEN `WL = 0` SUBST1_TAC THENL
     [UNDISCH_TAC `WL * (2 * (R * R + u1 * u1)) <= Q * ((R * R + 2 * u0 * R) - u1 * u1)` THEN
      ASM_SIMP_TAC[ARITH_RULE `a <= b ==> a - b = 0`; MULT_CLAUSES; LE] THEN
      REWRITE_TAC[MULT_EQ_0] THEN
      SUBGOAL_THEN `~(2 * (R * R + u1 * u1) = 0)` (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `2 * x = 0 <=> x = 0`; ADD_EQ_0; MULT_EQ_0] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN
    MP_TAC(SPECL [`t:real`; `&1`; `t:real`; `&1`] REAL_LE_MUL2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE] o
    check (fun th -> can (find_term ((=) `WL:num`)) (concl th))) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&((R * R + 2 * u0 * R) - u1 * u1) =
                &(R * R + 2 * u0 * R) - &(u1 * u1)` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  ABBREV_TAC `t0 = &u0 / &R` THEN ABBREV_TAC `t1 = &u1 / &R` THEN
  SUBGOAL_THEN `&u0 = t0 * &R /\ &u1 = t1 * &R` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["t0"; "t1"] THEN
    UNDISCH_TAC `&0 < &R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `RR = &R` THEN ABBREV_TAC `QQ = &Q` THEN ABBREV_TAC `ww = &WL` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `ww * &2 * (&1 + t1 * t1) <= QQ * (&1 + &2 * t0 - t1 * t1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < RR * RR` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ (ASSUME `&0 < RR * RR`))] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `ww:real` (concl th) &&
                                            is_binary "real_le" (concl th))) THEN MATCH_MP_TAC(REAL_ARITH `x = a /\ y = b ==> a <= b ==> x <= y`) THEN
    CONJ_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ww` ASSUME_TAC THENL
   [EXPAND_TAC "ww" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `t * t <= t1 * t1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ww * &2 * (&1 + t * t) <= ww * &2 * (&1 + t1 * t1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `QQ * (&1 + &2 * t0 - t1 * t1) <= QQ * (&1 - t * t + &2 * t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The leaf lemma: clipping by the walls.                                    *)
(* ------------------------------------------------------------------------- *)

let MAX_DIV_LE = prove
 (`forall a b Q c. 0 < Q ==> (&(MAX a b) / &Q <= c <=> &a / &Q <= c /\ &b / &Q <= c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE; NOT_LE; GSYM REAL_OF_NUM_LT]) THEN
  ASM_REAL_ARITH_TAC);;

let LE_MIN_DIV = prove
 (`forall a b Q c. 0 < Q ==> (c <= &(MIN a b) / &Q <=> c <= &a / &Q /\ c <= &b / &Q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE; NOT_LE; GSYM REAL_OF_NUM_LT]) THEN
  ASM_REAL_ARITH_TAC);;

let LE_SUB_DIV = prove
 (`forall M WL Q c. 0 < Q /\ c <= &M / &Q - &WL / &Q ==> c <= &(M - WL) / &Q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M / &Q - &WL / &Q` THEN
  ASM_REWRITE_TAC[REAL_ARITH `a / q - b / q = (a - b) / q`] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  ASM_CASES_TAC `(WL:num) <= M` THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; REAL_LE_REFL]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  ASM_SIMP_TAC[ARITH_RULE `M < WL ==> M - WL = 0`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LT]) THEN ASM_REAL_ARITH_TAC);;

let BOXCOV_LEAF = prove
 (`forall pts:num->real^2 wt N m Q R M x0 x1 y0 y1 u0 u1 WL xl xh yl yh.
        0 < Q /\ 0 < R /\ u0 <= u1 /\ u1 <= R /\ m = &M / &Q /\
        WL * (2 * (R * R + u1 * u1)) <= Q * ((R * R + 2 * u0 * R) - u1 * u1) /\
        xl = MAX x0 WL /\ xh = MIN x1 (M - WL) /\
        yl = MAX y0 WL /\ yh = MIN y1 (M - WL) /\
        (forall c1 c2 t. &xl / &Q <= c1 /\ c1 <= &xh / &Q /\
                   &yl / &Q <= c2 /\ c2 <= &yh / &Q /\
                   &u0 / &R <= t /\ t <= &u1 / &R
                   ==> &1 <= capt pts wt N (tsq c1 c2 t))
        ==> boxcov pts wt N m Q R x0 x1 y0 y1 u0 u1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[boxcov] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`Q:num`; `R:num`; `u0:num`; `u1:num`; `WL:num`; `t:real`]
               WALL_LB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MAX_DIV_LE; LE_MIN_DIV] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  MATCH_MP_TAC LE_SUB_DIV THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `m = &M / &Q` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_REAL_ARITH_TAC);;

let BOXCOV_LEAF_EMPTY = prove
 (`forall pts:num->real^2 wt N Q R u0 u1 xl xh yl yh.
        0 < Q /\ (xh < xl \/ yh < yl)
        ==> forall c1 c2 t. &xl / &Q <= c1 /\ c1 <= &xh / &Q /\
                      &yl / &Q <= c2 /\ c2 <= &yh / &Q /\
                      &u0 / &R <= t /\ t <= &u1 / &R
                      ==> &1 <= capt pts wt N (tsq c1 c2 t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&xh / &Q < &xl / &Q \/ &yh / &Q < &yl / &Q` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV2_EQ]; REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Claimed points.                                                           *)
(* ------------------------------------------------------------------------- *)

let sorted_lt = define
 `(sorted_lt [] <=> true) /\
  (sorted_lt (CONS (a:num) t) <=> (t = [] \/ a < HD t) /\ sorted_lt t)`;;

let INCR_ALL_LT = prove
 (`forall t a. sorted_lt (CONS a t) ==> ALL (\k. a < k) t`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[ALL]; ALL_TAC] THEN
  X_GEN_TAC `a:num` THEN ONCE_REWRITE_TAC[sorted_lt] THEN
  REWRITE_TAC[HD; NOT_CONS_NIL; ALL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_ALL THEN GEN_TAC THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `a < (h:num)` THEN ARITH_TAC);;

let INCR_SUM = prove
 (`forall ks f. sorted_lt ks
          ==> sum (set_of_list ks) f = ITLIST (\k a. f k + a) ks (&0)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[set_of_list; ITLIST; SUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_SET_OF_LIST] THEN
  SUBGOAL_THEN `~((h:num) IN set_of_list t)` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP INCR_ALL_LT) THEN
    REWRITE_TAC[GSYM ALL_MEM; IN_SET_OF_LIST] THEN MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `sorted_lt (CONS h t)` THEN SIMP_TAC[sorted_lt]);;

let CLAIM_LE_CAPT = prove
 (`forall pts:num->real^2 wt N S ks.
        (forall k. k < N ==> &0 <= wt k) /\
        ALL (\k. k < N /\ pts k IN S) ks /\ sorted_lt ks
        ==> ITLIST (\k a. wt k + a) ks (&0) <= capt pts wt N S`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[capt] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (set_of_list ks)
                  (\k. if (pts:num->real^2) k IN S then (wt:num->real) k else &0)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[INCR_SUM] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`ks:num list`,`ks:num list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; ALL] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_SET_OF_LIST; IN_ELIM_THM;
                IN_DIFF] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ALL (\k. k < N /\ (pts:num->real^2) k IN S) ks` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
      ASM_MESON_TAC[REAL_LE_REFL]]]);;

let ITLIST_DIV = prove
 (`forall ks f W. ITLIST (\k a. &(f k) / &W + a) ks (&0) =
            &(ITLIST (\k a. f k + a) ks 0) / &W`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; real_div; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Forms of the leaf lemmas convenient for instantiation.                    *)
(* ------------------------------------------------------------------------- *)

let PT_NAT_LEAF = prove
 (`forall Q R u0 u1 xl xh yl yh a0 b0 g0 a1 b1 g1 a2 b2 g2.
        0 < Q /\ 0 < R /\ u0 <= u1 /\ u1 <= R /\
        a0 = 2 * (R * R - u0 * u0) /\ b0 = 2 * R * (u0 + u0) /\ g0 = R * R + u0 * u0 /\
        a1 = 2 * (R * R - u1 * u1) /\ b1 = 2 * R * (u1 + u1) /\ g1 = R * R + u1 * u1 /\
        a2 = 2 * (R * R - u0 * u1) /\ b2 = 2 * R * (u0 + u1) /\ g2 = R * R + u0 * u1
        ==> forall X Y.
             a0 * X + b0 * Y <= g0 * Q + a0 * xl + b0 * yl /\
             a0 * xh + b0 * yh <= g0 * Q + a0 * X + b0 * Y /\
             a0 * Y + b0 * xh <= g0 * Q + a0 * yl + b0 * X /\
             a0 * yh + b0 * X <= g0 * Q + a0 * Y + b0 * xl /\
             a1 * X + b1 * Y <= g1 * Q + a1 * xl + b1 * yl /\
             a1 * xh + b1 * yh <= g1 * Q + a1 * X + b1 * Y /\
             a1 * Y + b1 * xh <= g1 * Q + a1 * yl + b1 * X /\
             a1 * yh + b1 * X <= g1 * Q + a1 * Y + b1 * xl /\
             a2 * X + b2 * Y <= g2 * Q + a2 * xl + b2 * yl /\
             a2 * xh + b2 * yh <= g2 * Q + a2 * X + b2 * Y /\
             a2 * Y + b2 * xh <= g2 * Q + a2 * yl + b2 * X /\
             a2 * yh + b2 * X <= g2 * Q + a2 * Y + b2 * xl
             ==> forall c1 c2 t. &xl / &Q <= c1 /\ c1 <= &xh / &Q /\
                           &yl / &Q <= c2 /\ c2 <= &yh / &Q /\
                           &u0 / &R <= t /\ t <= &u1 / &R
                           ==> vector[&X / &Q; &Y / &Q] IN tsq c1 c2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC PT_NAT THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`a0:num`; `b0:num`; `g0:num`; `a1:num`; `b1:num`; `g1:num`;
                        `a2:num`; `b2:num`; `g2:num`] THEN
  ASM_REWRITE_TAC[]);;

let ALL_CLAIM_NIL = prove
 (`forall N (pts:num->real^2) S. ALL (\k. k < N /\ pts k IN S) []`,
  REWRITE_TAC[ALL]);;

let ALL_CLAIM_CONS = prove
 (`forall N (pts:num->real^2) S h t.
        (h < N /\ pts h IN S) /\ ALL (\k. k < N /\ pts k IN S) t
        ==> ALL (\k. k < N /\ pts k IN S) (CONS h t)`,
  REWRITE_TAC[ALL]);;

let CLAIM_CAPT_GE1 = prove
 (`forall pts:num->real^2 wt N S ks.
        (forall k. k < N ==> &0 <= wt k) /\
        ALL (\k. k < N /\ pts k IN S) ks /\ sorted_lt ks /\
        &1 <= ITLIST (\k a. wt k + a) ks (&0)
        ==> &1 <= capt pts wt N S`,
  MESON_TAC[CLAIM_LE_CAPT; REAL_LE_TRANS]);;

let FORALL_LT_0 = prove
 (`forall P. forall k. k < 0 ==> P k`,
  REWRITE_TAC[LT]);;

let FORALL_LT_SUC = prove
 (`forall P n. (forall k. k < n ==> P k) /\ P n ==> (forall k. k < SUC n ==> P k)`,
  REWRITE_TAC[LT] THEN MESON_TAC[]);;

let SUM_LT_SUC_DIV = prove
 (`forall wt n s w W. sum {k | k < n} wt = &s / &W /\ wt n = &w / &W
                ==> sum {k | k < SUC n} wt = &(w + s) / &W`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{k | k < SUC n} = n INSERT {k | k < n}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; LT]; ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let SUM_LT_0 = prove
 (`forall wt W. sum {k | k < 0} wt = &0 / &W`,
  REWRITE_TAC[LT; EMPTY_GSPEC; SUM_CLAUSES; real_div; REAL_MUL_LZERO]);;

let LE_ONE_DIV = prove
 (`forall n W. 0 < W /\ W <= n ==> &1 <= &n / &W`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; REAL_MUL_LID; REAL_OF_NUM_LE]);;

let EL_STEP = prove
 (`forall (L:A list) h t k. (forall i. EL (i + k) L = EL i (CONS h t))
                      ==> (forall i. EL (i + SUC k) L = EL i t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
  REWRITE_TAC[ADD_CLAUSES; EL; TL]);;

let EL_HEAD = prove
 (`forall (L:A list) h t k. (forall i. EL (i + k) L = EL i (CONS h t)) ==> EL k L = h`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[ADD_CLAUSES; EL; HD]);;

let EL_START = prove
 (`forall (L:A list). (forall i. EL (i + 0) L = EL i L)`,
  REWRITE_TAC[ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Rectangles of points: the twelve tests at the worst corners imply them    *)
(* for every grid point of the rectangle.                                    *)
(* ------------------------------------------------------------------------- *)

let MONO_LE_MULT = prove
 (`forall a X Xb:num. X <= Xb ==> a * X <= a * Xb`,
  SIMP_TAC[LE_MULT_LCANCEL]);;

let RECT_C1 = prove
 (`forall a b X Y Xb Yb K:num. a * Xb + b * Yb <= K /\ X <= Xb /\ Y <= Yb
                         ==> a * X + b * Y <= K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `X:num`; `Xb:num`] MONO_LE_MULT) THEN
  MP_TAC(SPECL [`b:num`; `Y:num`; `Yb:num`] MONO_LE_MULT) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RECT_C2 = prove
 (`forall a b X Y Xa Ya L G:num. L <= G + a * Xa + b * Ya /\ Xa <= X /\ Ya <= Y
                           ==> L <= G + a * X + b * Y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `Xa:num`; `X:num`] MONO_LE_MULT) THEN
  MP_TAC(SPECL [`b:num`; `Ya:num`; `Y:num`] MONO_LE_MULT) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RECT_C3 = prove
 (`forall a b X Y Xa Yb B G A:num. a * Yb + B <= G + A + b * Xa /\ Xa <= X /\ Y <= Yb
                             ==> a * Y + B <= G + A + b * X`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `Y:num`; `Yb:num`] MONO_LE_MULT) THEN
  MP_TAC(SPECL [`b:num`; `Xa:num`; `X:num`] MONO_LE_MULT) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RECT_C4 = prove
 (`forall a b X Y Xb Ya A G xl:num. A + b * Xb <= G + a * Ya + b * xl /\ X <= Xb /\ Ya <= Y
                             ==> A + b * X <= G + a * Y + b * xl`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:num`; `X:num`; `Xb:num`] MONO_LE_MULT) THEN
  MP_TAC(SPECL [`a:num`; `Ya:num`; `Y:num`] MONO_LE_MULT) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PT_RECT_LEAF = prove
 (`forall Q R u0 u1 xl xh yl yh a0 b0 g0 a1 b1 g1 a2 b2 g2.
        0 < Q /\ 0 < R /\ u0 <= u1 /\ u1 <= R /\
        a0 = 2 * (R * R - u0 * u0) /\ b0 = 2 * R * (u0 + u0) /\ g0 = R * R + u0 * u0 /\
        a1 = 2 * (R * R - u1 * u1) /\ b1 = 2 * R * (u1 + u1) /\ g1 = R * R + u1 * u1 /\
        a2 = 2 * (R * R - u0 * u1) /\ b2 = 2 * R * (u0 + u1) /\ g2 = R * R + u0 * u1
        ==> forall Xa Xb Ya Yb.
             a0 * Xb + b0 * Yb <= g0 * Q + a0 * xl + b0 * yl /\
             a0 * xh + b0 * yh <= g0 * Q + a0 * Xa + b0 * Ya /\
             a0 * Yb + b0 * xh <= g0 * Q + a0 * yl + b0 * Xa /\
             a0 * yh + b0 * Xb <= g0 * Q + a0 * Ya + b0 * xl /\
             a1 * Xb + b1 * Yb <= g1 * Q + a1 * xl + b1 * yl /\
             a1 * xh + b1 * yh <= g1 * Q + a1 * Xa + b1 * Ya /\
             a1 * Yb + b1 * xh <= g1 * Q + a1 * yl + b1 * Xa /\
             a1 * yh + b1 * Xb <= g1 * Q + a1 * Ya + b1 * xl /\
             a2 * Xb + b2 * Yb <= g2 * Q + a2 * xl + b2 * yl /\
             a2 * xh + b2 * yh <= g2 * Q + a2 * Xa + b2 * Ya /\
             a2 * Yb + b2 * xh <= g2 * Q + a2 * yl + b2 * Xa /\
             a2 * yh + b2 * Xb <= g2 * Q + a2 * Ya + b2 * xl
             ==> forall X Y. Xa <= X /\ X <= Xb /\ Ya <= Y /\ Y <= Yb
                       ==> forall c1 c2 t. &xl / &Q <= c1 /\ c1 <= &xh / &Q /\
                                     &yl / &Q <= c2 /\ c2 <= &yh / &Q /\
                                     &u0 / &R <= t /\ t <= &u1 / &R
                                     ==> vector[&X / &Q; &Y / &Q] IN tsq c1 c2 t`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MP (SPEC_ALL PT_NAT_LEAF)) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`X:num`; `Y:num`]) THEN
  MATCH_MP_TAC(TAUT `a ==> (a ==> b) ==> b`) THEN
  REPEAT CONJ_TAC THEN
  FIRST [MATCH_MP_TAC RECT_C1 THEN MAP_EVERY EXISTS_TAC [`Xb:num`; `Yb:num`] THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC RECT_C2 THEN MAP_EVERY EXISTS_TAC [`Xa:num`; `Ya:num`] THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC RECT_C3 THEN MAP_EVERY EXISTS_TAC [`Xa:num`; `Yb:num`] THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC RECT_C4 THEN MAP_EVERY EXISTS_TAC [`Xb:num`; `Ya:num`] THEN
         ASM_REWRITE_TAC[] THEN NO_TAC]);;

let RECT_MEMBER = prove
 (`forall (P:num->num->bool) Xa Xb Ya Yb X Y.
        (forall X Y. Xa <= X /\ X <= Xb /\ Ya <= Y /\ Y <= Yb ==> P X Y) /\
        Xa <= X /\ X <= Xb /\ Ya <= Y /\ Y <= Yb ==> P X Y`,
  MESON_TAC[]);;
