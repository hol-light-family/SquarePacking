(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/MergedReduction.lean.         *)
(* Initial merged-owner reductions from the original C983 entrance.          *)
(* Conventions of CP_OtherCases_C983_F4Filters.ml: actual p i =              *)
(* c983e_actual c1 c2 a b l i, (domains i).allowed = EL i                    *)
(* c983e_domain_allowed, originalComponents i = EL i                         *)
(* c983e_original_components, owners p 7 / 8 / 11 = owner 2304 / 4096 /      *)
(* 32768.  MergedNearTopPoint.point = OCMNTP_POINT, left_aux =               *)
(* C983AB_LEFT_AUX, point_exact via oo_aux_point, merged_no_f3 =             *)
(* C983MTE_MERGED_NO_F3, merged_no_g6 = C983MG6_MERGED_NO_G6, f4_top_exact = *)
(* C983F4CE_F4_TOP_EXACT.  Tag C983MR_.                                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_MergedTopExclusion.ml";;
needs "n12/geometry/CP_OtherCases_C983_MergedG6Exclusion.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4CentralEntrance.ml";;
needs "n12/geometry/CP_OtherCases_MergedNearTopPoint.ml";;

let c983mr_stmt hyps concl =
  mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(list_mk_conj ([C983F4F_NP; C983F4F_IMG] @ hyps), concl)));;
let c983mr_use th hs =
  MP (SPECL C983E_VARS th) (end_itlist CONJ (ASSUME C983F4F_NP :: ASSUME C983F4F_IMG :: hs));;

(* Lean: merged_g7_check (private) *)
let C983MR_MERGED_G7_CHECK = prove
 (`forall s. MEM s (EL 7 c983e_domain_allowed) ==> ~(17 IN s)`,
  REWRITE_TAC[c983e_domain_allowed] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[MEM] THEN GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: merged_no_g7 *)
let C983MR_MERGED_NO_G7 = c983f4f_close (c983mr_stmt [] (mk_neg (c983f4f_mem 17 7)))
  (MATCH_MP C983MR_MERGED_G7_CHECK
     (MP (SPECL (C983E_VARS @ [`7`]) C983E_ACTUAL_MEM)
         (CONJ (ASSUME C983F4F_NP) (CONJ (ASSUME C983F4F_IMG) (c983f4f_lt 7)))));;

(* Lean: merged_g4_implies_f5 *)
let c983mr_g4_implies_f5 g4 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let cap = MP (SPECL C983E_VARS OO_SIDE_LE) (ASSUME C983F4F_NP) in
  let left = MP (SPECL C983E_VARS C983AB_LEFT_AUX) (c983f4f_hh ()) in
  let point = MP (SPECL (c983ab_own 2304) OCMNTP_POINT)
    (end_itlist CONJ [unit 2304; pos; side; cap; seed 7 `&33 / &20` `&33 / &20`;
                      c983f4f_point g4; excl 2304 4096 (CONJUNCT1 left)]) in
  let mem = EQ_MP (SPECL (C983E_VARS @ [`2304`]) (oo_aux_point 5))
              (CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) point) in
  EQ_MP (SYM (C983F4F_ACT_CONV (c983f4f_mem 5 7))) mem;;
let C983MR_MERGED_G4_IMPLIES_F5 = c983f4f_close (c983mr_stmt [c983f4f_mem 14 7] (c983f4f_mem 5 7))
  (c983mr_g4_implies_f5 (ASSUME (c983f4f_mem 14 7)));;

(* Lean: merged_f4_no_g4 *)
let c983mr_f4_no_g4 f4 =
  let ex = c983mr_use C983F4CE_F4_TOP_EXACT [f4] in
  let top = EQT_ELIM ((REWRITE_CONV[ex; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) (c983f4f_mem 14 11)) in
  c983f4f_absent 11 7 top;;
let C983MR_MERGED_F4_NO_G4 = c983f4f_close (c983mr_stmt [c983f4f_mem 4 7] (mk_neg (c983f4f_mem 14 7)))
  (c983mr_f4_no_g4 (ASSUME (c983f4f_mem 4 7)));;

(* Lean: mergedInitialComponents *)
let c983mr_merged_initial_components = new_definition
 `c983mr_merged_initial_components : (num->bool)list = [{13}; {4, 13}; {5, 13}; {4, 5, 13}; {5, 13, 14}]`;;

(* Lean: merged_reduction_check (private) *)
let C983MR_MERGED_REDUCTION_CHECK = prove
 (`forall s. MEM s (EL 7 c983e_original_components) ==> ~(3 IN s) ==> ~(16 IN s) ==> ~(17 IN s) ==>
       (14 IN s ==> 5 IN s) ==> (4 IN s ==> ~(14 IN s)) ==> MEM s c983mr_merged_initial_components`,
  REWRITE_TAC[c983mr_merged_initial_components] THEN c983f4f_check_tac);;

(* Lean: merged_initial_components *)
let C983MR_MERGED_INITIAL_COMPONENTS =
  let g4 = mk_comb(`(IN) 14`, c983f4f_act 7) and f4 = c983f4f_mem 4 7 in
  let imp1 = DISCH g4 (c983mr_g4_implies_f5 (ASSUME g4)) in
  let imp2 = DISCH f4 (c983mr_f4_no_g4 (ASSUME f4)) in
  let th = itlist (fun a t -> MP t a) (rev
    [c983mr_use C983MTE_MERGED_NO_F3 []; c983mr_use C983MG6_MERGED_NO_G6 [];
     c983mr_use C983MR_MERGED_NO_G7 []; imp1; imp2])
    (MATCH_MP C983MR_MERGED_REDUCTION_CHECK (c983f4f_orig 7)) in
  c983f4f_close (c983mr_stmt []
    (mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, c983f4f_act 7), `c983mr_merged_initial_components`)))
    th;;
