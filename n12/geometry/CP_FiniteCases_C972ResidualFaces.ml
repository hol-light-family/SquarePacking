(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972ResidualFaces.lean             *)
(* (namespace N12Compact.FiniteCases.C972).  Simultaneous faces in the      *)
(* single remaining C972 configuration.  Conventions of                      *)
(* CP_FiniteCases_C972SoutheastPositive.ml / C972SouthwestPositive.ml        *)
(* (owners p 5 / 6 = masks 256 / 512, OpenSquares A, E = cA .., cE .. with   *)
(* C972SP_SQ_A / C972SP_SQ_E: unit normal, positive side, side = l and the   *)
(* actual equivalence; Normal = c977cc_normal).  fixed C972CS_FIXED          *)
(* (C972CS_FIXED_TAC), foreign / apart C972CS_CLASH_TAC; southeast_missing_ *)
(* halfpoint / left_origin C972UE_*; southeast_g6_of_missing_halfpoint       *)
(* C972SR_*; right_origin C972UR_RIGHT_ORIGIN; southeast_g8 C972CS_*;        *)
(* C1090.ResidualCentralPoints.mixed_point C1090RCP_MIXED_POINT;             *)
(* southwest_positive_cap C972SS_SOUTHWEST_POSITIVE_CAP; southwest_positive_ *)
(* input C972SWP_*; C1092MPPMInwardPositive.profile C1092IPP_PROFILE;        *)
(* southeast_support_profile C972SP_SOUTHEAST_SUPPORT_PROFILE                *)
(* (c983fss_data).  Tag C972RF_.                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972SouthwestPositive.ml";;

let c972rf_head c th = is_comb (concl th) && fst (strip_comb (concl th)) = c;;
let C972RF_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: southeast_inner *)
let C972RF_SOUTHEAST_INNER = prove
 (c972mc_stmt [] (c972mc_own 512 `&113 / &50` `&2`),
  MESON_TAC[C972SR_SOUTHEAST_G6_OF_MISSING_HALFPOINT; C972UE_SOUTHEAST_MISSING_HALFPOINT]);;

(* Lean: southeast_mixed_point *)
let C972RF_SOUTHEAST_MIXED_POINT = prove
 (c972mc_stmt [] (c972mc_own 512 `&54 / &25` `&79 / &50`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN
  MP_TAC(SPEC_ALL C972RF_SOUTHEAST_INNER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972UR_RIGHT_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_OWNER_TAC 512 THEN
  MP_TAC(SPECL (c972ss_tr22 (c983ld_sw (c972ur_py (c972ss_tuple 512)))) C1090RCP_MIXED_POINT) THEN
  REWRITE_TAC[C972NF_TRANSLATED] THEN REWRITE_TAC[LINSIDE_PULLSW] THEN REWRITE_TAC[LINSIDE_PULLY] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN C972CS_SIDE_TAC);;

let C972RF_NORMAL_TAC c s =
  let n = list_mk_comb(`c977cc_normal`, [c; s]) in
  STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (ASSUME n)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] (ASSUME n));;

(* Lean: southwest_sharp_faces *)
let C972RF_SOUTHWEST_SHARP_FACES = prove
 (c972swp_stmt C972SP_A (C972SP_SQ_A @ [`c977cc_normal cA sA`])
   `uA + aA <= (&4 / &25) * cA - (&21 / &50) * sA /\ vA + aA <= (&4 / &25) * cA + (&21 / &50) * sA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_USE_TAC C972MC_V5 C972UE_SOUTHEAST_MISSING_HALFPOINT THEN
  C972SP_USE_TAC C972MC_V5 C972RF_SOUTHEAST_MIXED_POINT THEN
  C972RF_NORMAL_TAC `cA:real` `sA:real` THEN
  C972CS_FIXED_TAC THEN
  SUBGOAL_THEN `&0 < cA` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (C972MC_V5 @ C972SP_A) C972SS_SOUTHWEST_POSITIVE_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `linside cA sA uA vA aA (&0) (--(&13 / &50))` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[linside] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `vA < --(&4 / &25) * sA - (&21 / &50) * cA` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; RASM_ARITH_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linside cA sA uA vA aA (&4 / &25) (--(&21 / &50))` MP_TAC THENL
   [REWRITE_TAC[linside] THEN C972RF_LP_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_TAC THEN C972CS_CLASH_TAC);;

(* Lean: southwest_left_origin_cap *)
let C972RF_SOUTHWEST_LEFT_ORIGIN_CAP = prove
 (c972swp_stmt C972SP_A (C972SP_SQ_A @ [`c977cc_normal cA sA`]) `vA + aA <= sA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_A) C972SWP_SOUTHWEST_POSITIVE_INPUT THEN
  C972SP_USE_TAC C972MC_V5 C972UE_LEFT_ORIGIN THEN
  MP_TAC(SPECL C972SP_A C1092IPP_PROFILE) THEN ASM_REWRITE_TAC[c1092ipp_profile] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipp_input] o check (c972rf_head `c1092ipp_input`)) THEN
  C972RF_NORMAL_TAC `cA:real` `sA:real` THEN
  MAP_EVERY (fun tm -> MP_TAC(REWRITE_RULE[linside] (ASSUME tm)) THEN STRIP_TAC)
    [`linside cA sA uA vA aA (--(&7 / &20)) (--(&7 / &20))`; `linside cA sA uA vA aA (&0) (--(&13 / &50))`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linside cA sA uA vA aA (--(&1)) (&0)` MP_TAC THENL
   [REWRITE_TAC[linside] THEN C972RF_LP_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_TAC THEN C972CS_CLASH_TAC);;

(* Lean: southeast_lower_face *)
let C972RF_SOUTHEAST_LOWER_FACE = prove
 (c972swp_stmt C972SP_E (C972SP_SQ_E @ [`c977cc_normal cE sE`]) `--sE - cE / &2 <= vE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_USE_TAC C972MC_V5 C972UE_SOUTHEAST_MISSING_HALFPOINT THEN
  C972SP_USE_TAC C972MC_V5 C972CS_SOUTHEAST_G8 THEN
  C972CS_FIXED_TAC THEN C972RF_NORMAL_TAC `cE:real` `sE:real` THEN
  SUBGOAL_THEN `linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\ linside cE sE uE vE aE (&1) (--(&2 / &5))`
    MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[linside] THEN STRIP_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linside cE sE uE vE aE (&1) (--(&1 / &2))` MP_TAC THENL
   [REWRITE_TAC[linside] THEN C972RF_LP_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;

(* Lean: southeast_height_positive *)
let C972RF_SOUTHEAST_HEIGHT_POSITIVE = prove
 (c972swp_stmt C972SP_E (C972SP_SQ_E @ [`c977cc_normal cE sE`]) `&0 < vE + aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_USE_TAC C972MC_V5 C972UE_SOUTHEAST_MISSING_HALFPOINT THEN
  C972RF_NORMAL_TAC `cE:real` `sE:real` THEN
  SUBGOAL_THEN `&0 < cE /\ abs sE <= cE` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[real_abs] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_E) C972SP_SOUTHEAST_SUPPORT_PROFILE THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_E) C972RF_SOUTHEAST_LOWER_FACE THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c983fss_data] o check (c972rf_head `c983fss_data`)) THEN
  MP_TAC C972MC_SIDE THEN RASM_ARITH_TAC);;
