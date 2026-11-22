(* ========================================================================= *)
(* Port of Compact/Bridge/CoverageReorder.lean (N12Compact.PrefixCoverage). *)
(* Reordering the same twelve owners puts the constrained wall domains       *)
(* before the central domains.  Lean List.take / List.drop are cro_take /    *)
(* cro_drop; List.Perm is cro_perm (equal occurrence counts of every value,  *)
(* i.e. Lean's List.perm_iff_count); List.Forall2 is ALL2, List.Pairwise is  *)
(* PAIRWISE, Disjoint is DISJOINT.                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/PrefixCoverage.ml";;

(* Lean: List.take *)
let cro_take = new_recursive_definition list_RECURSION
 `(cro_take (n:num) ([]:A list) = []) /\
  (cro_take n (CONS h t) = if n = 0 then [] else CONS h (cro_take (n - 1) t))`;;

(* Lean: List.drop *)
let cro_drop = new_recursive_definition list_RECURSION
 `(cro_drop (n:num) ([]:A list) = []) /\
  (cro_drop n (CONS h t) = if n = 0 then CONS h t else cro_drop (n - 1) t)`;;

(* Lean: List.Perm (via List.perm_iff_count) *)
let cro_perm = new_definition
 `cro_perm (l1:A list) l2 <=>
    forall x. LENGTH (FILTER (\y. y = x) l1) = LENGTH (FILTER (\y. y = x) l2)`;;

(* Lean: reorder *)
let cro_reorder = new_definition
 `cro_reorder (v:A list) =
    APPEND (cro_take 2 v) (APPEND (cro_drop 6 (cro_drop 2 v)) (cro_take 6 (cro_drop 2 v)))`;;

(* Lean: unorder *)
let cro_unorder = new_definition
 `cro_unorder (v:A list) =
    APPEND (cro_take 2 v) (APPEND (cro_drop 4 (cro_drop 2 v)) (cro_take 4 (cro_drop 2 v)))`;;

(* Lean: List.take_append_drop *)
let CRO_TAKE_APPEND_DROP = prove
 (`forall (l:A list) n. APPEND (cro_take n l) (cro_drop n l) = l`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[cro_take; cro_drop; APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

(* Lean: List.forall₂_take *)
let CRO_ALL2_TAKE = prove
 (`forall (R:A->B->bool) a ds n. ALL2 R a ds ==> ALL2 R (cro_take n a) (cro_take n ds)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; cro_take] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ALL2]);;

(* Lean: List.forall₂_drop *)
let CRO_ALL2_DROP = prove
 (`forall (R:A->B->bool) a ds n. ALL2 R a ds ==> ALL2 R (cro_drop n a) (cro_drop n ds)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; cro_drop] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ALL2]);;

(* Lean: List.rel_append *)
let CRO_ALL2_APPEND = prove
 (`forall (R:A->B->bool) a c b d. ALL2 R a c /\ ALL2 R b d ==> ALL2 R (APPEND a b) (APPEND c d)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; APPEND] THEN ASM_MESON_TAC[]);;

let CRO_COUNT_APPEND = prove
 (`forall (l:A list) m x. LENGTH (FILTER (\y. y = x) (APPEND l m)) =
                    LENGTH (FILTER (\y. y = x) l) + LENGTH (FILTER (\y. y = x) m)`,
  REWRITE_TAC[FILTER_APPEND; LENGTH_APPEND]);;

let CRO_COUNT_SPLIT = prove
 (`forall (l:A list) n x. LENGTH (FILTER (\y. y = x) l) =
                    LENGTH (FILTER (\y. y = x) (cro_take n l)) +
                    LENGTH (FILTER (\y. y = x) (cro_drop n l))`,
  REWRITE_TAC[GSYM CRO_COUNT_APPEND; CRO_TAKE_APPEND_DROP]);;

(* Lean: reorder_perm *)
let CRO_REORDER_PERM = prove
 (`forall v:A list. cro_perm (cro_reorder v) v`,
  GEN_TAC THEN REWRITE_TAC[cro_perm; cro_reorder; CRO_COUNT_APPEND] THEN GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [SPECL [`v:A list`; `2`] CRO_COUNT_SPLIT] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SPECL [`cro_drop 2 (v:A list)`; `6`] CRO_COUNT_SPLIT] THEN
  ARITH_TAC);;

(* Lean: reorder_allowed *)
let CRO_REORDER_ALLOWED = prove
 (`forall (R:A->B->bool) a ds. ALL2 R a ds ==> ALL2 R (cro_reorder a) (cro_reorder ds)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cro_reorder] THEN
  REPEAT (MATCH_MP_TAC CRO_ALL2_APPEND THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[CRO_ALL2_TAKE; CRO_ALL2_DROP]);;

(* Lean: reorder_pairwise *)
let CRO_REORDER_PAIRWISE = prove
 (`forall v:((num->bool)list). PAIRWISE DISJOINT v ==> PAIRWISE DISJOINT (cro_reorder v)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [SYM(ISPECL [`v:(num->bool)list`; `2`] CRO_TAKE_APPEND_DROP)] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
    [SYM(ISPECL [`cro_drop 2 (v:(num->bool)list)`; `6`] CRO_TAKE_APPEND_DROP)] THEN
  REWRITE_TAC[cro_reorder; PAIRWISE_APPEND; MEM_APPEND] THEN
  MESON_TAC[DISJOINT_SYM]);;

(* Lean: unorder_reorder *)
let CRO_UNORDER_REORDER = prove
 (`forall v:A list. LENGTH v = 12 ==> cro_unorder (cro_reorder v) = v`,
  GEN_TAC THEN
  CONV_TAC (LAND_CONV (RAND_CONV (TOP_DEPTH_CONV num_CONV))) THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[cro_unorder; cro_reorder] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC[cro_take; cro_drop; APPEND] THEN CONV_TAC NUM_REDUCE_CONV)));;
