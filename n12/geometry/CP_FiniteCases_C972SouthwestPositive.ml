(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972SouthwestPositive.lean         *)
(* (namespace N12Compact.FiniteCases.C972).  C972 has a positive,            *)
(* missing-center inward southwest square.  Conventions of                   *)
(* CP_FiniteCases_C972SoutheastPositive.ml (A = cA sA uA vA aA with unit     *)
(* normal and positive side explicit; owners p 5 = owner 256; Normal =       *)
(* c977cc_normal).  C1092MPPMInwardPositive.Input / Profile / profile =      *)
(* c1092ipp_input / c1092ipp_profile / C1092IPP_PROFILE; southwest_center_   *)
(* missing = C972SC_*, southeast_missing_halfpoint / northeast_origin =      *)
(* C972UE_*, southwest_negative_center_of_northeast_origin = C972SWC_*,      *)
(* southwest_strong_tips = C972SS_*, singleton_vertical / horizontal =       *)
(* C972O_SINGLETON_* (C972CS_SV / SH).  Tag C972SWP_.                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972SoutheastCentered.ml";;
needs "n12/geometry/CP_FiniteCases_C972SouthwestCenters.ml";;
needs "n12/geometry/CP_FiniteCases_C972UpperEnding.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveProfile.ml";;

let c972swp_stmt vars hyps body =
  list_mk_forall(C972MC_V5 @ vars, mk_imp(list_mk_conj([C972MC_NP; C972MC_IMG] @ hyps), body));;

(* Lean: southwest_missing_center *)
let C972SWP_SOUTHWEST_MISSING_CENTER = prove
 (c972swp_stmt [] [] (mk_neg (c972mc_own 256 `&2` `&2`)),
  MESON_TAC[C972SC_SOUTHWEST_CENTER_MISSING; C972UE_SOUTHEAST_MISSING_HALFPOINT]);;

(* Lean: southwest_positive *)
let C972SWP_SOUTHWEST_POSITIVE = prove
 (c972swp_stmt C972SP_A (C972SP_SQ_A @ [`&0 < cA`; `abs sA <= cA`]) `&0 < sA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_USE_TAC C972MC_V5 C972UE_NORTHEAST_ORIGIN THEN
  C972SP_USE_TAC C972MC_V5 C972SWP_SOUTHWEST_MISSING_CENTER THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c977cc_normal cA (--sA)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN
    UNDISCH_TAC `cA * cA + sA * sA = &1` THEN UNDISCH_TAC `abs sA <= cA` THEN
    UNDISCH_TAC `sA <= &0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_A) C972SWC_SOUTHWEST_NEGATIVE_CENTER_OF_NORTHEAST_ORIGIN THEN
  UNDISCH_TAC `linside cA sA uA vA aA (&0) (&0)` THEN
  REWRITE_TAC[ASSUME C972SP_ACT_A] THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: exists_positive_southwest *)
let C972SWP_EXISTS_POSITIVE_SOUTHWEST = prove
 (c972swp_stmt [] []
    (list_mk_exists(C972SP_A, list_mk_conj (C972SP_SQ_A @ [`c977cc_normal cA sA`; `&0 < sA`]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL (c972ss_tr22 (c972mc_tuple 256)) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ACCEPT_TAC (c972mc_unit 256); MP_TAC C972MC_SIDE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C972SP_A THEN STRIP_TAC THEN
  SUBGOAL_THEN C972SP_ACT_A ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `linside`)) (concl th)
                           then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[C972NF_TRANSLATED]; ALL_TAC] THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_A) C972SWP_SOUTHWEST_POSITIVE THEN
  MAP_EVERY EXISTS_TAC C972SP_A THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC]);;

(* Lean: southwest_positive_input *)
let C972SWP_SOUTHWEST_POSITIVE_INPUT = prove
 (c972swp_stmt C972SP_A (C972SP_SQ_A @ [`c977cc_normal cA sA`]) (list_mk_comb(`c1092ipp_input`, C972SP_A)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_USE_TAC C972MC_V5 C972SWP_SOUTHWEST_MISSING_CENTER THEN
  C972SP_USE_TAC C972MC_V5 C972SS_SOUTHWEST_STRONG_TIPS THEN
  C972SP_USE_TAC C972MC_V5 C972CS_SOUTHWEST_WEST THEN
  REWRITE_TAC[c1092ipp_input; ASSUME C972SP_ACT_A] THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  C972CS_FIXED_TAC THEN C972CS_SH `&8 / &5` THEN C972CS_SV `&8 / &5` THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC THEN C972CS_CLASH_TAC; RASM_ARITH_TAC]);;

(* Lean: southwest_positive_profile *)
let C972SWP_SOUTHWEST_POSITIVE_PROFILE = prove
 (c972swp_stmt C972SP_A (C972SP_SQ_A @ [`c977cc_normal cA sA`]) (list_mk_comb(`c1092ipp_profile`, C972SP_A)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1092IPP_PROFILE THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_A) C972SWP_SOUTHWEST_POSITIVE_INPUT THEN
  ASM_REWRITE_TAC[]);;
