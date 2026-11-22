(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972SoutheastReduction.lean        *)
(* (namespace N12Compact.FiniteCases.C972).  Further C972 deductions in the  *)
(* original twelve owners (residual reductions, not an exclusion).           *)
(* owners p i = owner of mask EL i c972o_masks, written with the literal     *)
(* mask (owners 0..11 = masks 1,2,12,48,192,256,512,1024,2048,4096,8192,     *)
(* 16384).  fixed = C972CS_FIXED (C972CS_FIXED_TAC), foreign =               *)
(* C972CS_CLASH_TAC, OrdinaryMarkerHalfpoint.point_original =                *)
(* OCOMHM_POINT_ORIGINAL, F4PointTransfers.horizontal_original =             *)
(* OCF4PT_HORIZONTAL_ORIGINAL.  Tag C972SR_.                                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972UpperReduction.ml";;
needs "n12/geometry/CP_OtherCases_F4PointTransfers.ml";;

let c972sr_own = c972mc_own and c972sr_stmt = c972mc_stmt and c972sr_tuple = c972mc_tuple;;

(* Lean: southeast_halfpoint_of_missing_g6 *)
let C972SR_SOUTHEAST_HALFPOINT_OF_MISSING_G6 = prove
 (c972sr_stmt [mk_neg (c972sr_own 512 `&113 / &50` `&2`)] (c972sr_own 512 `&3` `&3 / &2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_SOUTHEAST_G8) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 512 THEN
  MATCH_MP_TAC (CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (SPECL (c972sr_tuple 512 @ [`&43 / &500`]) OCOMHM_POINT_ORIGINAL)) THEN
  C972MC_SIDE_TAC []);;

(* Lean: southeast_g6_of_missing_halfpoint *)
let C972SR_SOUTHEAST_G6_OF_MISSING_HALFPOINT = prove
 (c972sr_stmt [mk_neg (c972sr_own 512 `&3` `&3 / &2`)] (c972sr_own 512 `&113 / &50` `&2`),
  MESON_TAC[C972SR_SOUTHEAST_HALFPOINT_OF_MISSING_G6]);;

(* Lean: southeast_east_of_g6 *)
let C972SR_SOUTHEAST_EAST_OF_G6 = prove
 (c972sr_stmt [c972sr_own 512 `&113 / &50` `&2`] (c972sr_own 512 `&5 / &2` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_BOTTOM_REACH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&5 / &2` o CONJUNCT2) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 512 THEN
  MATCH_MP_TAC (SPECL (c972sr_tuple 512) OCF4PT_HORIZONTAL_ORIGINAL) THEN
  C972MC_SIDE_TAC []);;

(* Lean: northeast_origin_of_missing_southeast_halfpoint *)
let C972SR_NORTHEAST_ORIGIN_OF_MISSING_SOUTHEAST_HALFPOINT = prove
 (c972sr_stmt [mk_neg (c972sr_own 512 `&3` `&3 / &2`)] (c972sr_own 1024 `&2` `&3`),
  MESON_TAC[C972MC_SOUTHEAST_HALFPOINT_OF_NORTHEAST_MISSING_ORIGIN]);;

(* Lean: northwest_forward_of_southeast_halfpoint *)
let C972SR_NORTHWEST_FORWARD_OF_SOUTHEAST_HALFPOINT = prove
 (c972sr_stmt [c972sr_own 512 `&3` `&3 / &2`] (c972sr_own 2048 `&2` `&113 / &50`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972MC_ZERO_CORNER_OF_SOUTHEAST_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  MP_TAC(SPEC_ALL C972MC_ONE_CORNER_OF_NORTHWEST_MISSING_F5) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`&1`; `&1`] (c972mc_apart 1 2)) THEN ASM_REWRITE_TAC[]);;

(* Lean: southeast_alternative *)
let C972SR_SOUTHEAST_ALTERNATIVE = prove
 (c972sr_stmt []
   (mk_disj(c972sr_own 512 `&3` `&3 / &2`,
            list_mk_conj [c972sr_own 512 `&113 / &50` `&2`; c972sr_own 512 `&5 / &2` `&2`;
                          c972sr_own 1024 `&2` `&3`])),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (c972sr_own 512 `&3` `&3 / &2`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC_ALL C972SR_SOUTHEAST_G6_OF_MISSING_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[C972SR_SOUTHEAST_EAST_OF_G6; C972SR_NORTHEAST_ORIGIN_OF_MISSING_SOUTHEAST_HALFPOINT]);;

(* Lean: northwest_missing_southeast_points *)
let C972SR_NORTHWEST_MISSING_SOUTHEAST_POINTS = prove
 (c972sr_stmt [mk_neg (c972sr_own 2048 `&2` `&113 / &50`)]
   (list_mk_conj [c972sr_own 512 `&113 / &50` `&2`; c972sr_own 512 `&5 / &2` `&2`;
                  c972sr_own 1024 `&2` `&3`]),
  MESON_TAC[C972SR_SOUTHEAST_ALTERNATIVE; C972SR_NORTHWEST_FORWARD_OF_SOUTHEAST_HALFPOINT]);;
