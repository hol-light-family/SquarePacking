(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F4OutwardJoin.lean.           *)
(* The original C983 F4 join to the actual outward-pair theorem.             *)
(* Conventions of CP_OtherCases_C983_F4Filters.ml (actual p i =              *)
(* c983e_actual c1 c2 a b l i, originalComponents i = EL i                   *)
(* c983e_original_components, absent_of_foreign = c983f4f_absent).           *)
(* southeast_outward_pair_exclusion = C983AOP_SOUTHEAST_OUTWARD_PAIR_EXCLUSION,*)
(* f4_outward_northeast_f5 / f4_northeast_g7 = C983F4CE_*, f4_top_origin =   *)
(* C983FO_F4_TOP_ORIGIN.  Tag C983F4OJ_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4CentralEntrance.ml";;
needs "n12/geometry/CP_OtherCases_C983_ActualOutwardPair.ml";;

(* Lean: outward_exact_check (private) *)
let C983F4OJ_OUTWARD_EXACT_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==> ~(4 IN s) ==> ~(16 IN s) ==> s = {8, 18}`,
  c983f4f_check_tac);;

let c983f4oj_use th hs =
  MP (SPECL C983E_VARS th) (end_itlist CONJ (ASSUME C983F4F_NP :: ASSUME C983F4F_IMG :: hs));;

(* Lean: f4_southeast_g6 *)
let C983F4OJ_F4_SOUTHEAST_G6 =
  let f4 = ASSUME (c983f4f_mem 4 7) in
  let noG6 = ASSUME (mk_neg (c983f4f_mem 16 5)) in
  let outward = MP (MP (MATCH_MP C983F4OJ_OUTWARD_EXACT_CHECK (c983f4f_orig 5)) (c983f4f_absent 7 5 f4)) noG6 in
  let memo j = EQT_ELIM ((REWRITE_CONV[outward; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV)
                           (c983f4f_mem j 5)) in
  let f = c983f4oj_use C983AOP_SOUTHEAST_OUTWARD_PAIR_EXCLUSION
    [memo 8; memo 18; noG6; c983f4oj_use C983F4CE_F4_OUTWARD_NORTHEAST_F5 [f4; noG6];
     c983f4oj_use C983F4CE_F4_NORTHEAST_G7 [f4]; c983f4oj_use C983FO_F4_TOP_ORIGIN [f4]] in
  c983f4f_close
    (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
      mk_imp(list_mk_conj [C983F4F_NP; C983F4F_IMG; c983f4f_mem 4 7], c983f4f_mem 16 5))))
    (CCONTR (c983f4f_mem 16 5) f);;
