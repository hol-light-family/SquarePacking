(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/MergedG6Exclusion.lean         *)
(* (N12Compact.Completion.OtherCases.C983).  Complete elimination of G6     *)
(* from the actual merged C983 owner.  Conventions of                        *)
(* CP_OtherCases_C983_F4Filters.ml: actual p i = c983e_actual c1 c2 a b l i, *)
(* originalComponents i = EL i c983e_original_components, owners p 5 / 6 =   *)
(* owner 512 / 1024.  absent_of_foreign = c983f4f_absent                     *)
(* (C983F4F_ABSENT_OF_FOREIGN), original_actual_mem = c983f4f_orig,          *)
(* merged_g3 = C983F4F_MERGED_G3, top_origin_of_f3 = C983FO_TOP_ORIGIN_OF_F3,*)
(* right_bar_of_f8 = C983FO_RIGHT_BAR_OF_F8, southeast_outward_point /       *)
(* northeast_upper_point / southeast_inward_outward_exclusion = C983SA_*,    *)
(* southeast_outward_pair_exclusion = C983AOP_*, owners_apart 5 6 =          *)
(* oo_apart at masks 512 1024.  Tag C983MG6_.                                *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_ActualOutwardPair.ml";;

(* Lean: southeast_outward_check (private) *)
let C983MG6_SOUTHEAST_OUTWARD_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==> ~(16 IN s) ==> (4 IN s \/ 8 IN s) /\ 18 IN s`,
  c983f4f_check_tac);;

(* Lean: right_forced_check (private) *)
let C983MG6_RIGHT_FORCED_CHECK = prove
 (`forall s. MEM s (EL 10 c983e_original_components) ==> ~(8 IN s) ==> 9 IN s /\ 19 IN s`,
  c983f4f_check_tac);;

(* Lean: northeast_forced_check (private) *)
let C983MG6_NORTHEAST_FORCED_CHECK = prove
 (`forall s. MEM s (EL 6 c983e_original_components) ==>
       ~(16 IN s) ==> ~(9 IN s) ==> ~(19 IN s) ==> ~(13 IN s) ==> 17 IN s /\ (5 IN s \/ 7 IN s)`,
  c983f4f_check_tac);;

(* Lean: top_leftward_check (private) *)
let C983MG6_TOP_LEFTWARD_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> ~(17 IN s) ==> 3 IN s`,
  c983f4f_check_tac);;

(* apply a packing statement  !c1 c2 a b l. NPACK /\ IMAGE /\ h1 /\ .. ==> C  to theorems of h1 .. *)
let c983mg6_use th facts =
  MP (SPECL C983E_VARS th) (end_itlist CONJ ([ASSUME C983F4F_NP; ASSUME C983F4F_IMG] @ facts));;

(* from |- A \/ B and |- ~A  to  |- B *)
let c983mg6_res d n =
  let a = lhand (concl d) and b = rand (concl d) in
  DISJ_CASES d (CONTR b (MP (NOT_ELIM n) (ASSUME a))) (ASSUME b);;

let c983mg6_chk th i nots = itlist (fun a th -> MP th a) (rev nots) (MATCH_MP th (c983f4f_orig i));;

(* Lean: merged_no_g6 *)
let C983MG6_MERGED_NO_G6 =
  let g6 = ASSUME (c983f4f_mem 16 7) in
  let noG6 = c983f4f_absent 7 5 g6 in
  let outward = c983mg6_chk C983MG6_SOUTHEAST_OUTWARD_CHECK 5 [noG6] in
  let g18 = CONJUNCT2 outward in
  let noF4 = NOT_INTRO (DISCH (c983f4f_mem 4 5)
    (c983mg6_use C983SA_SOUTHEAST_INWARD_OUTWARD_EXCLUSION [ASSUME (c983f4f_mem 4 5); g18; noG6])) in
  let f8 = c983mg6_res (CONJUNCT1 outward) noF4 in
  let right = c983mg6_chk C983MG6_RIGHT_FORCED_CHECK 10 [c983f4f_absent 5 10 f8] in
  let g3 = c983mg6_use C983F4F_MERGED_G3 [] in
  let northeast = c983mg6_chk C983MG6_NORTHEAST_FORCED_CHECK 6
    [c983f4f_absent 7 6 g6; c983f4f_absent 10 6 (CONJUNCT1 right);
     c983f4f_absent 10 6 (CONJUNCT2 right); c983f4f_absent 7 6 g3] in
  let g17 = CONJUNCT1 northeast in
  let topF3 = c983mg6_chk C983MG6_TOP_LEFTWARD_CHECK 11 [c983f4f_absent 6 11 g17] in
  let topOrigin = c983mg6_use C983FO_TOP_ORIGIN_OF_F3 [topF3] in
  let f5tm = c983f4f_mem 5 6 in
  let case1 = c983mg6_use C983AOP_SOUTHEAST_OUTWARD_PAIR_EXCLUSION
    [f8; g18; noG6; ASSUME f5tm; g17; topOrigin] in
  let case2 =
    let nF5 = ASSUME (mk_neg f5tm) in
    let nF7 = c983mg6_res (CONJUNCT2 northeast) nF5 in
    let lower = c983mg6_use C983SA_SOUTHEAST_OUTWARD_POINT [f8; g18; noG6] in
    let bar = c983mg6_use C983FO_RIGHT_BAR_OF_F8 [f8; CONJUNCT1 right; CONJUNCT2 right] in
    let upper = c983mg6_use C983SA_NORTHEAST_UPPER_POINT [nF7; nF5; topOrigin; bar] in
    let apart = REWRITE_RULE[ldisj]
      (MP (SPECL C983E_VARS (oo_apart C983E_F 512 1024)) (c983f4f_hh ())) in
    MP (NOT_ELIM (SPECL [`&101 / &40`; `&17 / &8`] apart)) (CONJ lower upper) in
  let th = DISJ_CASES (SPEC f5tm EXCLUDED_MIDDLE) case1 case2 in
  c983f4f_close
    (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
      mk_imp(mk_conj(C983F4F_NP, C983F4F_IMG), mk_neg (c983f4f_mem 16 7)))))
    (NOT_INTRO (DISCH (c983f4f_mem 16 7) th));;
