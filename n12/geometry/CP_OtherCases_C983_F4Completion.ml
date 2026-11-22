(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4Completion.lean              *)
(* (N12Compact.Completion.OtherCases.C983).  Complete original-owner         *)
(* composition of the C983 F4 ending and the whole-case exclusion of C983    *)
(* (row 514).  Conventions of CP_OtherCases_C983_F4Filters.ml (actual p 7 =  *)
(* c983e_actual c1 c2 a b l 7, j IN actual p i = c983f4f_mem j i; owners    *)
(* p 0 / 5 / 7 / 9 = owner 1 / 512 / 2304 / 8192).  Used: f5_impossible =    *)
(* C983F5CO_F5_IMPOSSIBLE, f4_southeast_profile =                           *)
(* C983FUP_F4_SOUTHEAST_PROFILE, f4_bottom_singleton_seeds /                *)
(* f4_merged_center = C983FCE_*, f4_bottom_midpoint_excluded_of_frame =     *)
(* C983BMO_*, f4_outer_midpoint_of_frame / bottom_origin_of_southeast_outer *)
(* = C983F4OMO_*, C974LocalEnding.bottom_missing_corner_excluded_of_seeds =  *)
(* C983LE_*, merged_three_branches = C983TB_MERGED_THREE_BRANCHES,          *)
(* excludes_case = C983RI_EXCLUDES_CASE.  (Lean header: "uncompiled".)       *)
(* Tag C983F4CO_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4UniformProfile.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4OuterMidpointOriginal.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4BottomMidpointOriginal.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4CornerEntrance.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LocalEnding.ml";;
needs "n12/geometry/CP_OtherCases_C983_F5Completion.ml";;
needs "n12/geometry/CP_OtherCases_C983_ThreeBranches.ml";;
needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;

(* add the conclusion of  th  specialised at vars; every antecedent conjunct must be an assumption *)
let C983F4CO_USE_TAC vars th (asl, w as g) =
  let th1 = SPECL vars th in
  let ants = conjuncts (lhand (concl th1)) in
  let get t = try find (fun a -> aconv (concl a) t) (map snd asl)
              with Failure _ -> failwith ("C983F4CO_USE_TAC: " ^ string_of_term t) in
  ASSUME_TAC (MP th1 (end_itlist CONJ (map get ants))) g;;

let C983F4CO_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`];;

(* Lean: f4_impossible *)
let C983F4CO_F4_IMPOSSIBLE = prove
 (c983sa_stmt [c983f4f_mem 4 7] `false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC (c983f4f_mem 5 7) THENL
   [C983F4CO_USE_TAC C983E_VARS C983F5CO_F5_IMPOSSIBLE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  C983F4CO_USE_TAC C983E_VARS C983FUP_F4_SOUTHEAST_PROFILE THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cE:real` (X_CHOOSE_THEN `sE:real` (X_CHOOSE_THEN `uE:real`
    (X_CHOOSE_THEN `vE:real` (X_CHOOSE_THEN `aE:real` (X_CHOOSE_THEN `t:real`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))))) THEN
  C983F4CO_USE_TAC C983E_VARS C983FCE_F4_BOTTOM_SINGLETON_SEEDS THEN
  POP_ASSUM (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  C983F4CO_USE_TAC (C983E_VARS @ C983F4CO_E) C983BMO_F4_BOTTOM_MIDPOINT_EXCLUDED_OF_FRAME THEN
  C983F4CO_USE_TAC C983E_VARS C983FCE_F4_MERGED_CENTER THEN
  C983F4CO_USE_TAC (C983E_VARS @ C983F4CO_E) C983F4OMO_F4_OUTER_MIDPOINT_OF_FRAME THEN
  C983F4CO_USE_TAC C983E_VARS C983F4OMO_BOTTOM_ORIGIN_OF_SOUTHEAST_OUTER THEN
  C983F4CO_USE_TAC C983E_VARS C983LE_BOTTOM_MISSING_CORNER_EXCLUDED_OF_SEEDS THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* Lean: cover (local decide in family_impossible) *)
let C983F4CO_COVER = prove
 (`forall s. MEM s c983tb_merged_final_components ==> 4 IN s \/ 5 IN s`,
  REWRITE_TAC[c983tb_merged_final_components; MEM] THEN
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: family_impossible *)
let C983F4CO_FAMILY_IMPOSSIBLE = prove
 (`excl_fam c983ri_family`,
  REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  C983F4CO_USE_TAC C983E_VARS C983TB_MERGED_THREE_BRANCHES THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP C983F4CO_COVER) THENL
   [C983F4CO_USE_TAC C983E_VARS C983F4CO_F4_IMPOSSIBLE;
    C983F4CO_USE_TAC C983E_VARS C983F5CO_F5_IMPOSSIBLE] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* Lean: case_excluded *)
let C983F4CO_CASE_EXCLUDED = MP C983RI_EXCLUDES_CASE C983F4CO_FAMILY_IMPOSSIBLE;;

(* assembly form: row 514 (original id 983) is excluded *)
let C983F4CO_EXCLUDED_ROW = ri_excluded_row 514 C983F4CO_CASE_EXCLUDED;;
