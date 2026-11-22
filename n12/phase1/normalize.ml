(* ========================================================================= *)
(* Port, layer 0: a packing of 12 unit squares in side t < 4 gives 12        *)
(* pairwise disjoint open squares of common side l in (1, 1001/1000] whose   *)
(* closures lie in [0,4]^2 (Jatloe: UnitPacking.normalize).                  *)
(* ========================================================================= *)

needs "n12/phase1/markers.ml";;

let OSQ_SUBSET_INTERIOR_RSQ = prove
 (`forall c1 c2 a b. a * a + b * b = &1
               ==> osq c1 c2 a b (&1) SUBSET interior(rsq c1 c2 a b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[osq; rsq; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `osq c1 c2 a b (&1) =
    {z:real^2 | vector[a; b] dot z < &1 / &2 + c1 * a + c2 * b} INTER
    {z | vector[--a; --b] dot z < &1 / &2 - c1 * a - c2 * b} INTER
    {z | vector[--b; a] dot z < &1 / &2 + c2 * a - c1 * b} INTER
    {z | vector[b; --a] dot z < &1 / &2 - c2 * a + c1 * b}`
  SUBST1_TAC THENL
   [REWRITE_TAC[osq; EXTENSION; IN_INTER; IN_ELIM_THM; DOT_2; VECTOR_2] THEN
    REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[OPEN_HALFSPACE_LT]]);;

let OSQ_SCALE = prove
 (`forall c1 c2 a b k z:real^2. &0 < k
        ==> (z IN osq (k * c1) (k * c2) a b k <=> inv k % z IN osq c1 c2 a b (&1))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_MUL_COMPONENT] THEN
  SUBGOAL_THEN
   `forall x y. (x - k * c1) * a + (y - k * c2) * b = k * ((inv k * x - c1) * a + (inv k * y - c2) * b) /\
          (y - k * c2) * a - (x - k * c1) * b = k * ((inv k * y - c2) * a - (inv k * x - c1) * b)`
   (fun th -> REWRITE_TAC[th])
  THENL [REPEAT GEN_TAC THEN UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < k ==> abs k = k`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> (k * x < k / &2 <=> k * x < k * (&1 / &2))`;
               REAL_LT_LMUL_EQ]);;

let NPACK = new_definition
 `NPACK (c1:num->real) c2 a b l <=>
    &1 < l /\ l <= &1001 / &1000 /\
    (forall i. i < 12 ==> a i * a i + b i * b i = &1 /\ owalls (c1 i) (c2 i) (a i) (b i) l) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> DISJOINT (osq (c1 i) (c2 i) (a i) (b i) l)
                        (osq (c1 j) (c2 j) (a j) (b j) l))`;;

let PACKS12_NORMALIZE = prove
 (`forall t. packs 12 t /\ t < &4 ==> exists c1 c2 a b l. NPACK c1 c2 a b l`,
  GEN_TAC THEN REWRITE_TAC[packs] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `sq:num->real^2->bool` STRIP_ASSUME_TAC)
                             ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [MATCH_MP_TAC UNIT_SQUARE_IN_CONTAINER_POS THEN
    EXISTS_TAC `(sq:num->real^2->bool) 0` THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `forall i. exists c1 c2 a b. i < 12 ==>
          &0 <= a /\ &0 <= b /\ a * a + b * b = &1 /\
          (sq:num->real^2->bool) i = rsq c1 c2 a b /\
          (a + b) / &2 <= c1 /\ c1 <= t - (a + b) / &2 /\
          (a + b) / &2 <= c2 /\ c2 <= t - (a + b) / &2`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC UNIT_SQUARE_NORMAL THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:num->real` (X_CHOOSE_THEN `c2:num->real`
    (X_CHOOSE_THEN `a:num->real` (X_CHOOSE_TAC `b:num->real`)))) THEN
  ABBREV_TAC `k = min (&4 / t) (&1001 / &1000)` THEN
  SUBGOAL_THEN `&1 < k /\ k <= &1001 / &1000 /\ k <= &4 / t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k * t <= &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 / t * t` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\i. k * (c1:num->real) i`; `\i. k * (c2:num->real) i`;
    `a:num->real`; `b:num->real`; `k:real`] THEN
  REWRITE_TAC[NPACK] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      has_const "rsq" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[owalls] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MP_TAC(SPECL [`k:real`; `(c1:num->real) i`; `((a:num->real) i + b i) / &2`;
                  `t - ((a:num->real) i + b i) / &2`] BILIN) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [`k:real`; `(c2:num->real) i`; `((a:num->real) i + b i) / &2`;
                  `t - ((a:num->real) i + b i) / &2`] BILIN) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [`k:real`; `(a:num->real) i + b i`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `k * t <= &4` THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^2` THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[OSQ_SCALE] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> has_const "rsq" (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> has_const "rsq" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o
    check (fun th -> has_const "DISJOINT" (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `inv k % z:real^2`) THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[OSQ_SUBSET_INTERIOR_RSQ; SUBSET]);;

(* Layers 0 + 1 together: in a hypothetical packing of 12 unit squares in a  *)
(* square of side < 4, after normalization every square owns a marker, and   *)
(* distinct squares own disjoint sets of markers.                            *)

let PACKS12_MARKER_OWNERS = prove
 (`forall t. packs 12 t /\ t < &4
       ==> exists c1 c2 a b l.
             NPACK c1 c2 a b l /\
             (forall i. i < 12 ==> exists k. k < 16 /\
                                 marker k IN osq (c1 i) (c2 i) (a i) (b i) l) /\
             (forall i j k. i < 12 /\ j < 12 /\ ~(i = j) /\
                      marker k IN osq (c1 i) (c2 i) (a i) (b i) l
                      ==> ~(marker k IN osq (c1 j) (c2 j) (a j) (b j) l))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PACKS12_NORMALIZE) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[NPACK]) THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC MARKER_NONAVOID THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o
      check (fun th -> has_const "DISJOINT" (concl th))) THEN
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]]);;
