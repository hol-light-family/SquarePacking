(* ========================================================================= *)
(* Port of Compact/Geometry/SectionCapacity.lean (Jatloe, N12-jatloe).        *)
(* Long horizontal sections of squares in the container [0,4]^2 each        *)
(* contain one of the grid points 1,2,3; disjoint squares give 3m slots.     *)
(* Also ports affine_endpoint_nonnegative from source/S12/WallGeometry.lean. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: S12.affine_endpoint_nonnegative (source/S12/WallGeometry.lean) *)
let SCAP_AFFINE_ENDPOINT_NONNEG = prove
 (`forall a d v. &0 < a /\ (forall t. &0 < t /\ t < a ==> &0 <= v + d * t) ==> &0 <= v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `d * (a / &2) <= --v / &2` THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `a / &2`) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
   NLIN_TAC []; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--v / (&2 * d)`) THEN
  SUBGOAL_THEN `d * (--v / (&2 * d)) = --v / &2` MP_TAC THENL
  [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SPEC_TAC(`--v / (&2 * d)`,`t:real`) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MP_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ASM_REAL_ARITH_TAC]);;

(* Lean: interval_hits *)
let SCAP_INTERVAL_HITS = prove
 (`forall l u. &0 <= l /\ u <= &4 /\ &1 < u - l
         ==> exists j. j < 3 /\ l < &j + &1 /\ &j + &1 < u`,
  let tac n = EXISTS_TAC n THEN
    CONV_TAC(NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
    ASM_REAL_ARITH_TAC in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `l < &1` THENL [tac `0`; ALL_TAC] THEN
  ASM_CASES_TAC `l < &2` THENL [tac `1`; ALL_TAC] THEN
  ASM_CASES_TAC `l < &3` THENL [tac `2`; ASM_REAL_ARITH_TAC]);;

(* Lean: LongSection (definition) *)
let scap_longsec = new_definition
 `scap_longsec (c:real) s u v a h <=>
    exists l r. &1 < r - l /\ forall x. l < x /\ x < r ==> linside c s u v a x h`;;

(* Lean: section_hits *)
let SCAP_SECTION_HITS = prove
 (`forall c s u v a h. lcont c s u v a /\ scap_longsec c s u v a h
     ==> exists j. j < 3 /\ linside c s u v a (&j + &1) h`,
  REWRITE_TAC[lcont; scap_longsec] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
  [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
   MAP_EVERY EXISTS_TAC [`r - l`; `&1`] THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `linside c s u v a (l + t) h` MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r <= &4` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= &4 - r ==> r <= &4`) THEN
   MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
   MAP_EVERY EXISTS_TAC [`r - l`; `&1`] THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `linside c s u v a (r - t) h` MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`l:real`; `r:real`] SCAP_INTERVAL_HITS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* Lean: multi_cut_capacity
   (squares q : Fin n -> OpenSquare as num-indexed parameter families,
    cuts : Fin m -> R as a num-indexed family) *)
let SCAP_MULTI_CUT_CAPACITY = prove
 (`forall n m (cq:num->real) sq uq vq aq (cuts:num->real).
     (forall i. i < n ==> lcont (cq i) (sq i) (uq i) (vq i) (aq i)) /\
     (forall i j. i < n /\ j < n /\ ~(i = j)
            ==> ldisj (cq i) (sq i) (uq i) (vq i) (aq i)
                      (cq j) (sq j) (uq j) (vq j) (aq j)) /\
     (forall i. i < n ==> exists k. k < m /\
            scap_longsec (cq i) (sq i) (uq i) (vq i) (aq i) (cuts k))
     ==> n <= m * 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `forall i:num. i < (n:num) ==> exists k:num j:num. k < (m:num) /\ j < 3 /\
        linside ((cq:num->real) i) (sq i) (uq i) (vq i) (aq i) (&j + &1) (cuts k)`
  MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SCAP_SECTION_HITS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `kf:num->num` (X_CHOOSE_TAC `jf:num->num`)) THEN
  MP_TAC(ISPECL [`\i:num. (kf i:num, jf i:num)`; `{i:num | i < n}`]
    CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; PAIR_EQ] THEN
   MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
   ASM_CASES_TAC `x:num = y` THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC
    `forall i j. i < (n:num) /\ j < n /\ ~(i = j)
           ==> ldisj ((cq:num->real) i) (sq i) (uq i) (vq i) (aq i)
                     (cq j) (sq j) (uq j) (vq j) (aq j)` THEN
   DISCH_THEN(MP_TAC o SPECL [`x:num`; `y:num`]) THEN
   ASM_REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&(jf(x:num)) + &1`; `(cuts:num->real)(kf(x:num))`]) THEN
   REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th -> MP_TAC(SPEC `x:num` th) THEN MP_TAC(SPEC `y:num` th)) THEN
   ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CARD_NUMSEG_LT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `m * 3 = CARD({k:num | k < m} CROSS {j:num | j < 3})`
  SUBST1_TAC THENL
  [SIMP_TAC[CARD_CROSS; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CROSS; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[]);;

(* Lean: four_on_one_cut *)
let SCAP_FOUR_ON_ONE_CUT = prove
 (`forall (cq:num->real) sq uq vq aq h.
     (forall i. i < 4 ==> lcont (cq i) (sq i) (uq i) (vq i) (aq i)) /\
     (forall i j. i < 4 /\ j < 4 /\ ~(i = j)
            ==> ldisj (cq i) (sq i) (uq i) (vq i) (aq i)
                      (cq j) (sq j) (uq j) (vq j) (aq j)) /\
     (forall i. i < 4 ==> scap_longsec (cq i) (sq i) (uq i) (vq i) (aq i) h)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `1`; `cq:num->real`; `sq:num->real`; `uq:num->real`;
    `vq:num->real`; `aq:num->real`; `\k:num. (h:real)`]
    SCAP_MULTI_CUT_CAPACITY) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN ASM_SIMP_TAC[ARITH]);;

(* Lean: seven_on_two_cuts *)
let SCAP_SEVEN_ON_TWO_CUTS = prove
 (`forall (cq:num->real) sq uq vq aq h0 h1.
     (forall i. i < 7 ==> lcont (cq i) (sq i) (uq i) (vq i) (aq i)) /\
     (forall i j. i < 7 /\ j < 7 /\ ~(i = j)
            ==> ldisj (cq i) (sq i) (uq i) (vq i) (aq i)
                      (cq j) (sq j) (uq j) (vq j) (aq j)) /\
     (forall i. i < 7 ==> scap_longsec (cq i) (sq i) (uq i) (vq i) (aq i) h0 \/
                    scap_longsec (cq i) (sq i) (uq i) (vq i) (aq i) h1)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`7`; `2`; `cq:num->real`; `sq:num->real`; `uq:num->real`;
    `vq:num->real`; `aq:num->real`; `\k:num. if k = 0 then (h0:real) else h1`]
    SCAP_MULTI_CUT_CAPACITY) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
  [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ARITH];
   EXISTS_TAC `1` THEN ASM_REWRITE_TAC[ARITH]]);;
