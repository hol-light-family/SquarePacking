(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972NortheastPositiveFaces.lean    *)
(* (namespaces N12Compact.FiniteCases.C972Local and .C972).  Actual          *)
(* positive-NE faces.  Conventions of CP_FiniteCases_C972NortheastSign.ml    *)
(* (N = cN sN uN vN aN, owners p 7 = mask 1024, actual equivalence at        *)
(* (2+x, 2+y), Normal = c977cc_normal).  fixed C972CS_FIXED_TAC (missing_top *)
(* included), foreign C972CS_CLASH_TAC, northeast_origin C972UE_*,           *)
(* northeast_missing_f5 C972UR_*.  Tag C972NPF_.                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972NortheastSign.ml";;

(* Lean: PositiveNorth (structure) *)
let c972npf_positiveNorth = new_definition
 `c972npf_positiveNorth (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    (&13 / &50) * s <= u /\ v + a <= (&543 / &500) * c`;;

(* Lean: positive_north_faces *)
let C972NPF_POSITIVE_NORTH_FACES = prove
 (`forall cN sN uN vN aN. cN * cN + sN * sN = &1 /\ &0 < aN /\ &1 < aN /\ c977cc_normal cN sN /\
     linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\ linside cN sN uN vN aN (&0) (&1) /\
     ~linside cN sN uN vN aN (&0) (&13 / &50) /\ ~linside cN sN uN vN aN (&0) (&543 / &500) /\
     ~linside cN sN uN vN aN (--(&7 / &20)) (&7 / &20)
     ==> c972npf_positiveNorth cN sN uN vN aN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (c972nsg_head `c977cc_normal`)) THEN
  SUBGOAL_THEN `linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\ linside cN sN uN vN aN (&0) (&1)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[linside] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC] THEN
  SUBGOAL_THEN `(&13 / &50) * sN <= uN` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&13 / &50) * cN <= vN` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      c972nsg_not_tac `linside cN sN uN vN aN (&0) (&13 / &50)`; ALL_TAC] THEN
    SUBGOAL_THEN `uN + aN <= (&543 / &500) * sN` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      c972nsg_not_tac `linside cN sN uN vN aN (&0) (&543 / &500)`; ALL_TAC] THEN
    c972nsg_not_tac `linside cN sN uN vN aN (--(&7 / &20)) (&7 / &20)`; ALL_TAC] THEN
  SUBGOAL_THEN `vN + aN <= (&543 / &500) * cN` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    c972nsg_not_tac `linside cN sN uN vN aN (&0) (&543 / &500)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[c972npf_positiveNorth]);;

(* Lean: northeast_positive_faces *)
let C972NPF_NORTHEAST_POSITIVE_FACES = prove
 (c972swp_stmt C972NSG_N (C972NSG_SQ_N4 @ [`c977cc_normal cN sN`])
    (list_mk_comb(`c972npf_positiveNorth`, C972NSG_N)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC])
    [C972UE_NORTHEAST_ORIGIN; C972UR_NORTHEAST_MISSING_F5] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  C972CS_FIXED_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL C972NSG_N C972NPF_POSITIVE_NORTH_FACES) THEN
  REWRITE_TAC[ASSUME C972NSG_ACT_N] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC THEN C972CS_CLASH_TAC; RASM_ARITH_TAC]);;
