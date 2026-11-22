(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/ThreeBranches.lean.            *)
(* The original C983 merged-owner entrance to the three remaining endings.  *)
(* Conventions of CP_OtherCases_C983_F4Filters.ml (actual p 7 =              *)
(* c983e_actual c1 c2 a b l 7); mergedInitialComponents =                   *)
(* c983mr_merged_initial_components, merged_initial_components =            *)
(* C983MR_MERGED_INITIAL_COMPONENTS, merged_no_g4 = C983F5LR_MERGED_NO_G4,   *)
(* merged_inward_alternative = C983IA_MERGED_INWARD_ALTERNATIVE.  Tag C983TB_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5LowerRight.ml";;
needs "n12/geometry/CP_OtherCases_C983_InwardAlternative.ml";;

(* Lean: mergedFinalComponents *)
let c983tb_merged_final_components = new_definition
 `c983tb_merged_final_components : (num->bool)list = [{4, 13}; {5, 13}; {4, 5, 13}]`;;

(* Lean: merged_three_check (private) *)
let C983TB_MERGED_THREE_CHECK = prove
 (`forall s. MEM s c983mr_merged_initial_components ==> ~(14 IN s) ==> (4 IN s \/ 5 IN s) ==>
       MEM s c983tb_merged_final_components`,
  REWRITE_TAC[c983mr_merged_initial_components; c983tb_merged_final_components; MEM] THEN
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let c983tb_use th facts =
  MP (SPECL C983E_VARS th) (end_itlist CONJ ([ASSUME C983F4F_NP; ASSUME C983F4F_IMG] @ facts));;

(* Lean: merged_three_branches *)
let C983TB_MERGED_THREE_BRANCHES =
  let th = itlist (fun a t -> MP t a)
    (rev [c983tb_use C983F5LR_MERGED_NO_G4 []; c983tb_use C983IA_MERGED_INWARD_ALTERNATIVE []])
    (MATCH_MP C983TB_MERGED_THREE_CHECK (c983tb_use C983MR_MERGED_INITIAL_COMPONENTS [])) in
  c983f4f_close (c983sa_stmt []
    (mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, c983f4f_act 7), `c983tb_merged_final_components`)))
    th;;
