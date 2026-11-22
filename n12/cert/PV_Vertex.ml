(* ========================================================================= *)
(* W-F6, part 1: planar vertex enumeration (irreducible fact F6).            *)
(* Lean: Compact/Core/PlanarVertex.lean (det, negate, BoxNormals,            *)
(*       negative_slope, first_exit, vertex_below, Feasible, VertexBound,    *)
(*       nonnegative_of_vertices),                                           *)
(*       Compact/Core/PlanarVertexCheck.lean (sign, vertex, Vertex.eval,     *)
(*       denominator_positive, eval_identity, nonnegative_iff, positive_iff, *)
(*       Vertex.Feasible, feasible_iff, PairCheck, Check, Check.vertexBound, *)
(*       Check.sound),                                                       *)
(*       Compact/Core/PlanarVertexSparse.lean (vertex_swap, pairCheck_refl,  *)
(*       pairCheck_swap, triangle, triangle_all, UnorderedCheck.toCheck),    *)
(*       Compact/Core/PlanarBoundaryFilter.lean (LineExclusion, .Check,      *)
(*       forces_negative, pairCheck, FilterCheck, active, FilterCheck.cover, *)
(*       Check, Check.toCheck).                                              *)
(* Points of Fin 2 -> R are two reals px py; a Lean Vertex <x,y,den> is the  *)
(* integer triple (x, y, den).  Lean's Check ranges over                     *)
(* (base ++ forbidden.flatten).dedup; pv_check ranges over the list without  *)
(* dedup, which has the same members (the statements are identical).        *)
(* Design: n12/docs/cert_design.md (W-F6).  Tag PV_ / pv_.                       *)
(* ========================================================================= *)

needs "n12/cert/CR_Farkas.ml";;

(* Lean: PlanarVertex.det *)
let pv_det = new_definition `pv_det a b = cr_x a * cr_y b - cr_y a * cr_x b`;;

(* Lean: Row.slope  (direction d = (dx, dy)) *)
let pv_slope = new_definition
 `pv_slope r (dx:real) (dy:real) = real_of_int (cr_x r) * dx + real_of_int (cr_y r) * dy`;;

(* Lean: PlanarVertex.negate *)
let pv_negate = new_definition
 `pv_negate r = CRow (--(cr_x r)) (--(cr_y r)) (--(cr_c r)) false`;;

(* Lean: eval_advance  (advance p d t = p + t d) *)
let PV_EVAL_ADVANCE = prove
 (`forall r px py dx dy t. cr_eval r (px + t * dx) (py + t * dy) = cr_eval r px py + t * pv_slope r dx dy`,
  REWRITE_TAC[cr_eval; pv_slope] THEN REAL_ARITH_TAC);;

(* Lean: eval_negate *)
let PV_EVAL_NEGATE = prove
 (`forall r px py. cr_eval (pv_negate r) px py = --(cr_eval r px py)`,
  REWRITE_TAC[cr_eval; pv_negate; cr_x; cr_y; cr_c; int_neg_th] THEN REAL_ARITH_TAC);;

let PV_DET_REAL = prove
 (`forall a b. real_of_int (pv_det a b) =
         real_of_int (cr_x a) * real_of_int (cr_y b) - real_of_int (cr_y a) * real_of_int (cr_x b)`,
  REWRITE_TAC[pv_det; int_sub_th; int_mul_th]);;

(* Lean: det_negate_left, det_negate_right *)
let PV_DET_NEGATE = prove
 (`forall a b. pv_det (pv_negate a) b = --(pv_det a b) /\ pv_det a (pv_negate b) = --(pv_det a b)`,
  REWRITE_TAC[pv_det; pv_negate; cr_x; cr_y; cr_c] THEN INT_ARITH_TAC);;

(* Lean: BoxNormals *)
let pv_box = new_definition
 `pv_box rws <=>
    EX (\r. &0 < cr_x r /\ cr_y r = &0) rws /\ EX (\r. cr_x r < &0 /\ cr_y r = &0) rws /\
    EX (\r. cr_x r = &0 /\ &0 < cr_y r) rws /\ EX (\r. cr_x r = &0 /\ cr_y r < &0) rws`;;

let PV_MUL_NEG = prove
 (`forall x d. (&0 < x /\ d < &0) \/ (x < &0 /\ &0 < d) ==> x * d < &0`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`x:real`; `--d`] REAL_LT_MUL); MP_TAC(SPECL [`--x`; `d:real`] REAL_LT_MUL)] THEN
  ASM_REWRITE_TAC[REAL_NEG_GT0] THEN REAL_ARITH_TAC);;

let PV_MUL_NONPOS = prove
 (`forall t s. &0 <= t /\ s <= &0 ==> t * s <= &0`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`t:real`; `--s`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: negative_slope *)
let PV_NEGATIVE_SLOPE = prove
 (`forall rws dx dy. pv_box rws /\ ~(dx = &0 /\ dy = &0) ==> exists r. MEM r rws /\ pv_slope r dx dy < &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_box; GSYM EX_MEM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `r0:crow`) (CONJUNCTS_THEN2 (X_CHOOSE_TAC `r1:crow`)
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `r2:crow`) (X_CHOOSE_TAC `r3:crow`)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE INT_REAL_RULES) THEN
  SUBGOAL_THEN `dx < &0 \/ &0 < dx \/ (dx = &0 /\ (dy < &0 \/ &0 < dy))` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pv_slope] THEN STRIP_TAC THENL
   [EXISTS_TAC `r0:crow`; EXISTS_TAC `r1:crow`; EXISTS_TAC `r2:crow`; EXISTS_TAC `r3:crow`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_ADD_LID] THEN
  MATCH_MP_TAC PV_MUL_NEG THEN ASM_REWRITE_TAC[]);;

(* the finite minimum used in first_exit *)
let PV_LIST_MIN = prove
 (`forall (f:A->real) P l. (exists x. MEM x l /\ P x) ==> exists x. MEM x l /\ P x /\ forall y. MEM y l /\ P y ==> f x <= f y`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  ASM_CASES_TAC `exists x:A. MEM x t /\ P x` THENL
   [FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `exists x:A. MEM x t /\ P x`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
    ASM_CASES_TAC `(P:A->bool) h /\ (f:A->real) h < f m` THENL
     [EXISTS_TAC `h:A`; EXISTS_TAC `m:A`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; REAL_LE_TRANS; REAL_NOT_LT];
    ASM_MESON_TAC[REAL_LE_REFL]]);;

let PV_DIV_LEMMA = prove
 (`forall e sl. sl < &0 ==> e + e / --sl * sl = &0`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(--sl = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `--sl`] REAL_DIV_RMUL) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: first_exit *)
let PV_FIRST_EXIT = prove
 (`forall rws px py dx dy.
     pv_box rws /\ (forall r. MEM r rws ==> &0 <= cr_eval r px py) /\ ~(dx = &0 /\ dy = &0)
     ==> exists t r. &0 <= t /\ MEM r rws /\ pv_slope r dx dy < &0 /\
               cr_eval r (px + t * dx) (py + t * dy) = &0 /\
               forall s. MEM s rws ==> &0 <= cr_eval s (px + t * dx) (py + t * dy)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`rws:crow list`; `dx:real`; `dy:real`] PV_NEGATIVE_SLOPE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\r. cr_eval r px py / --(pv_slope r dx dy)`; `\r. pv_slope r dx dy < &0`;
                 `rws:crow list`] PV_LIST_MIN) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:crow` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `cr_eval r px py / --(pv_slope r dx dy)` THEN EXISTS_TAC `r:crow` THEN
  ASM_REWRITE_TAC[PV_EVAL_ADVANCE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PV_DIV_LEMMA THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:crow` THEN DISCH_TAC THEN
    ASM_CASES_TAC `pv_slope s dx dy < &0` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:crow`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < --(pv_slope s dx dy)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
      MP_TAC(SPECL [`cr_eval r px py / --(pv_slope r dx dy)`; `pv_slope s dx dy`] REAL_LE_MUL) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= cr_eval s px py` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC]]);;

(* second walk of vertex_below, along e * tangent(a) (e = 1 or -1) *)
let PV_WALK2 = prove
 (`forall rws tg a p1x p1y e.
     pv_box rws /\ MEM a rws /\ ~(real_of_int (cr_x a) = &0 /\ real_of_int (cr_y a) = &0) /\
     e * e = &1 /\
     (forall r. MEM r rws ==> &0 <= cr_eval r p1x p1y) /\ cr_eval a p1x p1y = &0 /\
     pv_slope tg (e * --real_of_int (cr_y a)) (e * real_of_int (cr_x a)) <= &0
     ==> exists b qx qy. MEM b rws /\ ~(pv_det a b = &0) /\ cr_eval a qx qy = &0 /\
                   cr_eval b qx qy = &0 /\ (forall r. MEM r rws ==> &0 <= cr_eval r qx qy) /\
                   cr_eval tg qx qy <= cr_eval tg p1x p1y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(e = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `e * e = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`rws:crow list`; `p1x:real`; `p1y:real`; `e * --real_of_int (cr_y a)`;
                `e * real_of_int (cr_x a)`] PV_FIRST_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ENTIRE; REAL_NEG_EQ_0] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `b:crow` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`b:crow`; `p1x + t1 * e * --real_of_int (cr_y a)`;
                        `p1y + t1 * e * real_of_int (cr_x a)`] THEN
  ASM_REWRITE_TAC[PV_EVAL_ADVANCE] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[int_eq; int_of_num_th; PV_DET_REAL] THEN DISCH_TAC THEN
    UNDISCH_TAC `pv_slope b (e * --real_of_int (cr_y a)) (e * real_of_int (cr_x a)) < &0` THEN
    REWRITE_TAC[pv_slope] THEN
    SUBGOAL_THEN `real_of_int (cr_x b) * e * --real_of_int (cr_y a) +
                  real_of_int (cr_y b) * e * real_of_int (cr_x a) =
                  e * (real_of_int (cr_x a) * real_of_int (cr_y b) -
                       real_of_int (cr_y a) * real_of_int (cr_x b))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL]];
    REWRITE_TAC[pv_slope] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> e + x <= e`) THEN MATCH_MP_TAC PV_MUL_NONPOS THEN
    ASM_REWRITE_TAC[]]);;

(* first walk of vertex_below, along any d with slope(target) <= 0 *)
let PV_WALK1 = prove
 (`forall rws tg px py dx dy.
     pv_box rws /\ (forall r. MEM r rws ==> &0 <= cr_eval r px py) /\ ~(dx = &0 /\ dy = &0) /\
     pv_slope tg dx dy <= &0
     ==> exists a b qx qy. MEM a rws /\ MEM b rws /\ ~(pv_det a b = &0) /\
                     cr_eval a qx qy = &0 /\ cr_eval b qx qy = &0 /\
                     (forall r. MEM r rws ==> &0 <= cr_eval r qx qy) /\
                     cr_eval tg qx qy <= cr_eval tg px py`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`rws:crow list`; `px:real`; `py:real`; `dx:real`; `dy:real`] PV_FIRST_EXIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `a:crow` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `cr_eval tg (px + t0 * dx) (py + t0 * dy) <= cr_eval tg px py` ASSUME_TAC THENL
   [REWRITE_TAC[PV_EVAL_ADVANCE] THEN MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> e + x <= e`) THEN
    MATCH_MP_TAC PV_MUL_NONPOS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(real_of_int (cr_x a) = &0 /\ real_of_int (cr_y a) = &0)` ASSUME_TAC THENL
   [STRIP_TAC THEN UNDISCH_TAC `pv_slope a dx dy < &0` THEN
    ASM_REWRITE_TAC[pv_slope] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `pv_slope tg (--real_of_int (cr_y a)) (real_of_int (cr_x a)) <= &0` THENL
   [MP_TAC(SPECL [`rws:crow list`; `tg:crow`; `a:crow`; `px + t0 * dx`; `py + t0 * dy`; `&1`] PV_WALK2);
    MP_TAC(SPECL [`rws:crow list`; `tg:crow`; `a:crow`; `px + t0 * dx`; `py + t0 * dy`; `-- &1`] PV_WALK2)] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN
  (ANTS_TAC THENL [UNDISCH_TAC `~(pv_slope tg (--real_of_int (cr_y a)) (real_of_int (cr_x a)) <= &0)` THEN
                   REWRITE_TAC[pv_slope] THEN REAL_ARITH_TAC; ALL_TAC] ORELSE
   (ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) ORELSE ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:crow` (X_CHOOSE_THEN `qx:real` (X_CHOOSE_THEN `qy:real`
    STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:crow`; `b:crow`; `qx:real`; `qy:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LE_TRANS]);;

(* Lean: vertex_below *)
let PV_VERTEX_BELOW = prove
 (`forall rws tg px py.
     pv_box rws /\ (forall r. MEM r rws ==> &0 <= cr_eval r px py)
     ==> exists a b qx qy. MEM a rws /\ MEM b rws /\ ~(pv_det a b = &0) /\
                     cr_eval a qx qy = &0 /\ cr_eval b qx qy = &0 /\
                     (forall r. MEM r rws ==> &0 <= cr_eval r qx qy) /\
                     cr_eval tg qx qy <= cr_eval tg px py`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= real_of_int (cr_x tg)` THENL
   [MATCH_MP_TAC PV_WALK1 THEN MAP_EVERY EXISTS_TAC [`-- &1`; `&0`];
    MATCH_MP_TAC PV_WALK1 THEN MAP_EVERY EXISTS_TAC [`&1`; `&0`]] THEN
  ASM_REWRITE_TAC[pv_slope] THEN ASM_REAL_ARITH_TAC);;

(* Lean: PlanarVertex.Feasible *)
let pv_feasible = new_definition
 `pv_feasible base forb px py <=>
    (forall r. MEM r base ==> &0 <= cr_eval r px py) /\
    (forall blk. MEM blk forb ==> ~(forall r. MEM r blk ==> &0 < cr_eval r px py))`;;

(* Lean: PlanarVertex.VertexBound *)
let pv_vertex_bound = new_definition
 `pv_vertex_bound base forb tg <=>
    forall a b. MEM a (APPEND base (lflat forb)) /\ MEM b (APPEND base (lflat forb)) /\ ~(pv_det a b = &0)
          ==> forall px py. cr_eval a px py = &0 /\ cr_eval b px py = &0 /\ pv_feasible base forb px py
                      ==> &0 <= cr_eval tg px py`;;

let PV_NEG_CASES = prove
 (`forall a a0 b b0. (a = a0 \/ a = pv_negate a0) /\ (b = b0 \/ b = pv_negate b0)
     ==> (pv_det a b = &0 <=> pv_det a0 b0 = &0) /\
         (forall x y. cr_eval a x y = &0 <=> cr_eval a0 x y = &0) /\
         (forall x y. cr_eval b x y = &0 <=> cr_eval b0 x y = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PV_DET_NEGATE; PV_EVAL_NEGATE; INT_NEG_EQ_0; REAL_NEG_EQ_0]);;

(* Lean: nonnegative_of_vertices *)
let PV_NONNEG_OF_VERTICES = prove
 (`forall base forb tg px py.
     pv_box base /\ pv_vertex_bound base forb tg /\ pv_feasible base forb px py
     ==> &0 <= cr_eval tg px py`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_vertex_bound] THEN STRIP_TAC THEN
  ABBREV_TAC `rws = APPEND base (MAP pv_negate (FILTER (\r. cr_eval r px py <= &0) (lflat forb)))` THEN
  SUBGOAL_THEN `forall r. MEM r rws <=> MEM r base \/
                    exists s. MEM s (lflat forb) /\ cr_eval s px py <= &0 /\ r = pv_negate s`
    ASSUME_TAC THENL
   [EXPAND_TAC "rws" THEN REWRITE_TAC[MEM_APPEND; MEM_MAP; MEM_FILTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pv_box rws` ASSUME_TAC THENL
   [UNDISCH_TAC `pv_box base` THEN REWRITE_TAC[pv_box; GSYM EX_MEM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `forall r. MEM r rws ==> &0 <= cr_eval r px py` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THENL
     [ASM_MESON_TAC[pv_feasible]; ASM_REWRITE_TAC[PV_EVAL_NEGATE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(forall r. MEM r base ==> MEM r rws) /\
                (forall s. MEM s (lflat forb) /\ cr_eval s px py <= &0 ==> MEM (pv_negate s) rws) /\
                (forall a. MEM a rws ==> exists a0. MEM a0 (APPEND base (lflat forb)) /\ (a = a0 \/ a = pv_negate a0))`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall (concl th) &&
     is_iff (snd (dest_forall (concl th))))) THEN
  MP_TAC(SPECL [`rws:crow list`; `tg:crow`; `px:real`; `py:real`] PV_VERTEX_BELOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:crow` (X_CHOOSE_THEN `b:crow` (X_CHOOSE_THEN `qx:real`
    (X_CHOOSE_THEN `qy:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `pv_feasible base forb qx qy` ASSUME_TAC THENL
   [REWRITE_TAC[pv_feasible] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `blk:crow list` THEN DISCH_TAC THEN
    UNDISCH_TAC `pv_feasible base forb px py` THEN REWRITE_TAC[pv_feasible] THEN
    DISCH_THEN(MP_TAC o SPEC `blk:crow list` o CONJUNCT2) THEN ASM_REWRITE_TAC[NOT_FORALL_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:crow` MP_TAC) THEN REWRITE_TAC[NOT_IMP; REAL_NOT_LT] THEN
    STRIP_TAC THEN EXISTS_TAC `r:crow` THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
    SUBGOAL_THEN `MEM (pv_negate r) rws` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_LFLAT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th ->
      can (find_term ((=) `qx:real`)) (concl th) && is_forall (concl th)))) THEN
    REWRITE_TAC[PV_EVAL_NEGATE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `a:crow` th) THEN MP_TAC(SPEC `b:crow` th)) o
    check (fun th -> can (find_term ((=) `pv_negate`)) (concl th) &&
                     can (find_term (fun t -> try fst(dest_var t) = "a0" with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:crow` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:crow` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:crow`; `a0:crow`; `b:crow`; `b0:crow`] PV_NEG_CASES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cr_eval tg qx qy` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:crow`; `b0:crow`] o check (fun th ->
    can (find_term ((=) `pv_feasible`)) (concl th) && is_forall (concl th))) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* PlanarVertexCheck                                                         *)
(* ------------------------------------------------------------------------- *)

(* Lean: PlanarVertexCheck.sign *)
let pv_sign = new_definition `pv_sign a b = if &0 <= pv_det a b then &1 else -- &1:int`;;

(* Lean: PlanarVertexCheck.vertex  (Vertex <x, y, denominator> = (x, y, den)) *)
let pv_vertex = new_definition
 `pv_vertex a b = (pv_sign a b * (cr_y a * cr_c b - cr_c a * cr_y b),
                   pv_sign a b * (cr_c a * cr_x b - cr_x a * cr_c b),
                   pv_sign a b * pv_det a b)`;;

(* Lean: Vertex.eval *)
let pv_veval = new_definition
 `pv_veval (v:int#int#int) r = cr_x r * FST v + cr_y r * FST (SND v) + cr_c r * SND (SND v)`;;

(* Lean: denominator_positive *)
let PV_DENOMINATOR_POSITIVE = prove
 (`forall a b. ~(pv_det a b = &0) ==> &0 < SND (SND (pv_vertex a b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_vertex; pv_sign] THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN INT_ARITH_TAC);;

(* Lean: eval_identity *)
let PV_EVAL_IDENTITY = prove
 (`forall a b r px py. cr_eval a px py = &0 /\ cr_eval b px py = &0
     ==> real_of_int (pv_veval (pv_vertex a b) r) =
         real_of_int (SND (SND (pv_vertex a b))) * cr_eval r px py`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cr_eval] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_of_int (cr_c a) = --(real_of_int (cr_x a) * px + real_of_int (cr_y a) * py) /\
                real_of_int (cr_c b) = --(real_of_int (cr_x b) * px + real_of_int (cr_y b) * py)`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pv_veval; pv_vertex; FST; SND; int_add_th; int_mul_th; int_sub_th; PV_DET_REAL] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let PV_POS_MUL_IFF = prove
 (`forall d e. &0 < d ==> (&0 <= d * e <=> &0 <= e) /\ (&0 < d * e <=> &0 < e)`,
  SIMP_TAC[REAL_LE_MUL_EQ; REAL_LT_MUL_EQ]);;

(* Lean: nonnegative_iff, positive_iff *)
let PV_SIGN_IFF = prove
 (`forall a b r px py. ~(pv_det a b = &0) /\ cr_eval a px py = &0 /\ cr_eval b px py = &0
     ==> (&0 <= pv_veval (pv_vertex a b) r <=> &0 <= cr_eval r px py) /\
         (&0 < pv_veval (pv_vertex a b) r <=> &0 < cr_eval r px py)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:crow`; `b:crow`] PV_DENOMINATOR_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[int_lt; int_le; int_of_num_th] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:crow`; `b:crow`; `r:crow`; `px:real`; `py:real`] PV_EVAL_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[PV_POS_MUL_IFF]);;

(* Lean: Vertex.Feasible *)
let pv_vfeasible = new_definition
 `pv_vfeasible v base forb <=>
    ALL (\r. &0 <= pv_veval v r) base /\ ALL (\blk. ~ALL (\r. &0 < pv_veval v r) blk) forb`;;

(* Lean: feasible_iff *)
let PV_FEASIBLE_IFF = prove
 (`forall a b base forb px py. ~(pv_det a b = &0) /\ cr_eval a px py = &0 /\ cr_eval b px py = &0
     ==> (pv_vfeasible (pv_vertex a b) base forb <=> pv_feasible base forb px py)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP PV_SIGN_IFF) THEN
  ASM_REWRITE_TAC[pv_vfeasible; pv_feasible; GSYM ALL_MEM]);;

(* Lean: PlanarVertexCheck.PairCheck *)
let pv_pair_check = new_definition
 `pv_pair_check base forb tgs a b <=>
    pv_det a b = &0 \/
    (pv_vfeasible (pv_vertex a b) base forb ==> ALL (\t. &0 <= pv_veval (pv_vertex a b) t) tgs)`;;

(* Lean: PlanarVertexCheck.Check *)
let pv_check = new_definition
 `pv_check base forb tgs <=>
    forall a b. MEM a (APPEND base (lflat forb)) /\ MEM b (APPEND base (lflat forb))
          ==> pv_pair_check base forb tgs a b`;;

(* Lean: Check.vertexBound *)
let PV_CHECK_VERTEXBOUND = prove
 (`forall base forb tgs tg. pv_check base forb tgs /\ MEM tg tgs ==> pv_vertex_bound base forb tg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_check; pv_vertex_bound; pv_pair_check] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:crow`; `b:crow`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`px:real`; `py:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:crow`; `b:crow`; `base:crow list`; `forb:(crow list)list`; `px:real`; `py:real`]
    PV_FEASIBLE_IFF) THEN
  MP_TAC(SPECL [`a:crow`; `b:crow`; `tg:crow`; `px:real`; `py:real`] PV_SIGN_IFF) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:crow`; `b:crow`]) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

(* Lean: Check.sound *)
let PV_CHECK_SOUND = prove
 (`forall base forb tgs px py.
     pv_check base forb tgs /\ pv_box base /\ pv_feasible base forb px py
     ==> forall tg. MEM tg tgs ==> &0 <= cr_eval tg px py`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PV_NONNEG_OF_VERTICES THEN
  MAP_EVERY EXISTS_TAC [`base:crow list`; `forb:(crow list)list`] THEN
  ASM_MESON_TAC[PV_CHECK_VERTEXBOUND]);;

(* ------------------------------------------------------------------------- *)
(* PlanarVertexSparse: unordered pairs                                       *)
(* ------------------------------------------------------------------------- *)

let PV_DET_SWAP = prove
 (`forall a b. pv_det b a = --(pv_det a b)`, REWRITE_TAC[pv_det] THEN INT_ARITH_TAC);;

(* Lean: vertex_swap *)
let PV_VERTEX_SWAP = prove
 (`forall a b. ~(pv_det a b = &0) ==> pv_vertex b a = pv_vertex a b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pv_vertex; pv_sign] THEN SUBST1_TAC(SPECL [`a:crow`; `b:crow`] PV_DET_SWAP) THEN
  ASM_CASES_TAC `&0 <= pv_det a b` THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `&0 <= --(pv_det a b) <=> ~(&0 <= pv_det a b)` SUBST1_TAC THENL
    [UNDISCH_TAC `~(pv_det a b = &0)` THEN INT_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[pv_det] THEN INT_ARITH_TAC);;

(* Lean: pairCheck_refl *)
let PV_PAIR_REFL = prove
 (`forall base forb tgs a. pv_pair_check base forb tgs a a`,
  REWRITE_TAC[pv_pair_check; pv_det] THEN INT_ARITH_TAC);;

(* Lean: pairCheck_swap *)
let PV_PAIR_SWAP = prove
 (`forall base forb tgs a b. pv_pair_check base forb tgs a b ==> pv_pair_check base forb tgs b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_pair_check] THEN
  SUBST1_TAC(SPECL [`a:crow`; `b:crow`] PV_DET_SWAP) THEN
  ASM_CASES_TAC `pv_det a b = &0` THEN ASM_REWRITE_TAC[INT_NEG_EQ_0] THEN
  ASM_SIMP_TAC[PV_VERTEX_SWAP]);;

(* Lean: PlanarVertexSparse.triangle *)
let pv_triangle = define
 `(pv_triangle (test:crow->crow->bool) [] <=> true) /\
  (pv_triangle test (CONS a rest) <=> ALL (test a) rest /\ pv_triangle test rest)`;;

(* Lean: triangle_all *)
let PV_TRIANGLE_ALL = prove
 (`forall test rws. (forall a. test a a) /\ (forall a b. test a b ==> test b a) /\ pv_triangle test rws
     ==> forall a b. MEM a rws /\ MEM b rws ==> test a b`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[pv_triangle; MEM; GSYM ALL_MEM] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: UnorderedCheck.toCheck (for any list containing the boundary rws) *)
let PV_TRIANGLE_CHECK = prove
 (`forall base forb tgs. pv_triangle (pv_pair_check base forb tgs) (APPEND base (lflat forb))
     ==> pv_check base forb tgs`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pv_check] THEN MATCH_MP_TAC PV_TRIANGLE_ALL THEN
  ASM_REWRITE_TAC[PV_PAIR_REFL; ETA_AX] THEN MATCH_ACCEPT_TAC PV_PAIR_SWAP);;

(* ------------------------------------------------------------------------- *)
(* PlanarBoundaryFilter: whole-line exclusions                               *)
(* ------------------------------------------------------------------------- *)

(* Lean: LineExclusion.Check  (hint = (baseIndex, scale, multiple)) *)
let pv_lx_check = new_definition
 `pv_lx_check (h:num#int#int) base bnd <=>
    FST h < LENGTH base /\
    &0 < FST (SND h) /\
    FST (SND h) * cr_x (EL (FST h) base) = SND (SND h) * cr_x bnd /\
    FST (SND h) * cr_y (EL (FST h) base) = SND (SND h) * cr_y bnd /\
    FST (SND h) * cr_c (EL (FST h) base) < SND (SND h) * cr_c bnd`;;

(* Lean: first_boundary_zero *)
let PV_VERTEX_ON_FIRST = prove
 (`forall a b. pv_veval (pv_vertex a b) a = &0`,
  REWRITE_TAC[pv_veval; pv_vertex; pv_det; FST; SND] THEN INT_ARITH_TAC);;

(* Lean: LineExclusion.forces_negative (real form) *)
let PV_LX_REAL = prove
 (`forall sc m rx ry rc ax ay ac vx vy vd.
     &0 < sc /\ sc * rx = m * ax /\ sc * ry = m * ay /\ sc * rc < m * ac /\
     ax * vx + ay * vy + ac * vd = &0 /\ &0 < vd
     ==> rx * vx + ry * vy + rc * vd < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sc * (rx * vx + ry * vy + rc * vd) = vd * (sc * rc - m * ac)` ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `vd * (sc * rc - m * ac) < &0` ASSUME_TAC THENL
   [MATCH_MP_TAC PV_MUL_NEG THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`sc:real`; `rx * vx + ry * vy + rc * vd`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: LineExclusion.pairCheck *)
let PV_LX_PAIRCHECK = prove
 (`forall h base forb tgs a b. pv_lx_check h base a ==> pv_pair_check base forb tgs a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_lx_check; pv_pair_check] THEN STRIP_TAC THEN
  ASM_CASES_TAC `pv_det a b = &0` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~p ==> (p ==> q)`) THEN
  REWRITE_TAC[pv_vfeasible; GSYM ALL_MEM; DE_MORGAN_THM] THEN DISJ1_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; INT_NOT_LE] THEN
  EXISTS_TAC `EL (FST (h:num#int#int)) (base:crow list)` THEN ASM_SIMP_TAC[MEM_EL] THEN
  MP_TAC(SPECL [`a:crow`; `b:crow`] PV_DENOMINATOR_POSITIVE) THEN
  MP_TAC(SPECL [`a:crow`; `b:crow`] PV_VERTEX_ON_FIRST) THEN ASM_REWRITE_TAC[pv_veval] THEN
  RULE_ASSUM_TAC(REWRITE_RULE INT_REAL_RULES) THEN REWRITE_TAC INT_REAL_RULES THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC PV_LX_REAL THEN
  MAP_EVERY EXISTS_TAC [`real_of_int (FST (SND (h:num#int#int)))`; `real_of_int (SND (SND (h:num#int#int)))`;
     `real_of_int (cr_x a)`; `real_of_int (cr_y a)`; `real_of_int (cr_c a)`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: PlanarBoundaryFilter.FilterCheck *)
let pv_filter = define
 `(pv_filter base [] [] <=> true) /\
  (pv_filter base [] (CONS (hh:(num#int#int)option) plan) <=> false) /\
  (pv_filter base (CONS (a:crow) rest) [] <=> false) /\
  (pv_filter base (CONS a rest) (CONS NONE plan) <=> pv_filter base rest plan) /\
  (pv_filter base (CONS a rest) (CONS (SOME h) plan) <=> pv_lx_check h base a /\ pv_filter base rest plan)`;;

(* Lean: PlanarBoundaryFilter.active *)
let pv_active = define
 `(pv_active [] (plan:((num#int#int)option)list) = []) /\
  (pv_active (CONS (a:crow) rest) [] = []) /\
  (pv_active (CONS a rest) (CONS NONE plan) = CONS a (pv_active rest plan)) /\
  (pv_active (CONS a rest) (CONS (SOME h) plan) = pv_active rest plan)`;;

(* Lean: FilterCheck.cover *)
let PV_FILTER_COVER = prove
 (`forall base rws plan. pv_filter base rws plan
     ==> forall a. MEM a rws ==> MEM a (pv_active rws plan) \/ exists h. pv_lx_check h base a`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[pv_filter] THEN
  STRUCT_CASES_TAC (ISPEC `h':(num#int#int)option` (cases "option")) THEN
  REWRITE_TAC[pv_filter; pv_active; MEM] THEN ASM_MESON_TAC[]);;

(* Lean: PlanarBoundaryFilter.Check (on the list without dedup) *)
let pv_fcheck = new_definition
 `pv_fcheck base forb tgs plan <=>
    pv_filter base (APPEND base (lflat forb)) plan /\
    pv_triangle (pv_pair_check base forb tgs) (pv_active (APPEND base (lflat forb)) plan)`;;

(* Lean: PlanarBoundaryFilter.Check.toCheck *)
let PV_FCHECK_CHECK = prove
 (`forall base forb tgs plan. pv_fcheck base forb tgs plan ==> pv_check base forb tgs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pv_fcheck; pv_check] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PV_FILTER_COVER) THEN
  MP_TAC(ISPECL [`pv_pair_check base forb tgs`; `pv_active (APPEND base (lflat forb)) plan`]
    PV_TRIANGLE_ALL) THEN
  ASM_REWRITE_TAC[PV_PAIR_REFL] THEN ANTS_TAC THENL [MATCH_ACCEPT_TAC PV_PAIR_SWAP; ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`a:crow`; `b:crow`] THEN STRIP_TAC THEN
  ASM_MESON_TAC[PV_LX_PAIRCHECK; PV_PAIR_SWAP]);;

(* ------------------------------------------------------------------------- *)
(* Executable (short-circuit) forms for CR_EVAL_CONV, proved equal.          *)
(* ------------------------------------------------------------------------- *)

let pv_base_ok = define
 `(pv_base_ok v [] <=> true) /\
  (pv_base_ok v (CONS r rs) <=> if &0 <= pv_veval v r then pv_base_ok v rs else false)`;;
let pv_blk_pos = define
 `(pv_blk_pos v [] <=> true) /\
  (pv_blk_pos v (CONS r rs) <=> if &0 < pv_veval v r then pv_blk_pos v rs else false)`;;
let pv_blks_ok = define
 `(pv_blks_ok v [] <=> true) /\
  (pv_blks_ok v (CONS b bs) <=> if pv_blk_pos v b then false else pv_blks_ok v bs)`;;

let PV_BASE_OK = prove
 (`forall v l. pv_base_ok v l <=> ALL (\r. &0 <= pv_veval v r) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pv_base_ok; ALL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
let PV_BLK_POS = prove
 (`forall v l. pv_blk_pos v l <=> ALL (\r. &0 < pv_veval v r) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pv_blk_pos; ALL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
let PV_BLKS_OK = prove
 (`forall v l. pv_blks_ok v l <=> ALL (\blk. ~ALL (\r. &0 < pv_veval v r) blk) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pv_blks_ok; ALL; PV_BLK_POS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let pv_vtx = new_definition
 `pv_vtx a b (d:int) =
    if &0 <= d then (cr_y a * cr_c b - cr_c a * cr_y b, cr_c a * cr_x b - cr_x a * cr_c b, d)
    else (cr_c a * cr_y b - cr_y a * cr_c b, cr_x a * cr_c b - cr_c a * cr_x b, --d)`;;

let PV_VTX = prove
 (`forall a b. pv_vtx a b (pv_det a b) = pv_vertex a b`,
  REWRITE_TAC[pv_vtx; pv_vertex; pv_sign] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN INT_ARITH_TAC);;

let pv_pc = new_definition
 `pv_pc base forb tgs a b <=>
    let d = pv_det a b in
    if d = &0 then true else
    let v = pv_vtx a b d in
    if pv_base_ok v base then (if pv_blks_ok v forb then pv_base_ok v tgs else true) else true`;;

let PV_PC = prove
 (`forall base forb tgs a b. pv_pc base forb tgs a b <=> pv_pair_check base forb tgs a b`,
  REWRITE_TAC[pv_pc; pv_pair_check; LET_DEF; LET_END_DEF; PV_VTX; pv_vfeasible; PV_BASE_OK;
              PV_BLKS_OK] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let pv_row = define
 `(pv_row base forb tgs (a:crow) [] <=> true) /\
  (pv_row base forb tgs a (CONS b bs) <=>
     if pv_pc base forb tgs a b then pv_row base forb tgs a bs else false)`;;
let pv_tri = define
 `(pv_tri base forb tgs [] <=> true) /\
  (pv_tri base forb tgs (CONS a rest) <=>
     if pv_row base forb tgs a rest then pv_tri base forb tgs rest else false)`;;

let PV_ROW = prove
 (`forall base forb tgs a l. pv_row base forb tgs a l <=> ALL (pv_pair_check base forb tgs a) l`,
  REPEAT GEN_TAC THEN SPEC_TAC(`l:crow list`,`l:crow list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pv_row; ALL; PV_PC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
let PV_TRI = prove
 (`forall base forb tgs l. pv_tri base forb tgs l <=> pv_triangle (pv_pair_check base forb tgs) l`,
  REPEAT GEN_TAC THEN SPEC_TAC(`l:crow list`,`l:crow list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pv_tri; pv_triangle; PV_ROW] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let pv_fast = new_definition
 `pv_fast base forb tgs plan <=>
    let L = APPEND base (lflat forb) in
    if pv_filter base L plan then pv_tri base forb tgs (pv_active L plan) else false`;;

let PV_FAST = prove
 (`forall base forb tgs plan. pv_fast base forb tgs plan <=> pv_fcheck base forb tgs plan`,
  REWRITE_TAC[pv_fast; pv_fcheck; LET_DEF; LET_END_DEF; PV_TRI] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
