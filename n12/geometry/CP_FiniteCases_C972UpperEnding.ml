(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972UpperEnding.lean               *)
(* (namespace N12Compact.FiniteCases.C972).  The missing NE top-origin       *)
(* branch is impossible.  owners p i = owner of mask EL i c972o_masks,       *)
(* written with the literal mask (owners 0..11 = masks 1,2,12,48,192,256,    *)
(* 512,1024,2048,4096,8192,16384).  fixed = C972CS_FIXED (C972CS_FIXED_TAC), *)
(* foreign / apart = C972CS_CLASH_TAC / c972mc_apart.  Used:                 *)
(* northwest_half_or_vertical / northwest_halfpoint_of_northeast_origin /   *)
(* one_corner_of_northeast_origin = C972NH_*, zero_corner_of_southeast_     *)
(* halfpoint / southeast_halfpoint_of_northeast_missing_origin /            *)
(* left_missing_impossible / left_origin_of_northwest_halfpoint = C972MC_*, *)
(* northeast_g7 / right_reach = C972CS_*, C981CompletionUpperPoint.point =   *)
(* C981UP_POINT.  Tag C972UE_.                                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972NorthwestHalfpoint.ml";;

(* Lean: northeast_origin *)
let C972UE_NORTHEAST_ORIGIN = prove
 (c972mc_stmt [] (c972mc_own 1024 `&2` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHEAST_G7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_RIGHT_REACH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 1024 THEN
  REFUTE_THEN ASSUME_TAC THEN
  MP_TAC(SPEC_ALL C972NH_NORTHWEST_HALF_OR_VERTICAL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(SPEC_ALL C972MC_SOUTHEAST_HALFPOINT_OF_NORTHEAST_MISSING_ORIGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC_ALL C972MC_ZERO_CORNER_OF_SOUTHEAST_HALFPOINT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC (c972mc_own 2 `&1` `&1`) THENL
     [MP_TAC(SPECL [`&1`; `&1`] (c972mc_apart 1 2)) THEN ASM_REWRITE_TAC[];
      MP_TAC(SPEC_ALL C972MC_LEFT_MISSING_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN (c972mc_own 1024 `&2` `&131 / &50`) ASSUME_TAC THENL
     [MATCH_MP_TAC (SPECL (c972mc_tuple 1024) C981UP_POINT) THEN
      REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC THEN C972CS_CLASH_TAC; RASM_ARITH_TAC];
      ALL_TAC] THEN
    C972CS_CLASH_TAC]);;

(* Lean: northwest_outer_halfpoint *)
let C972UE_NORTHWEST_OUTER_HALFPOINT = prove
 (c972mc_stmt [] (c972mc_own 2048 `&3 / &2` `&3`),
  MESON_TAC[C972UE_NORTHEAST_ORIGIN; C972NH_NORTHWEST_HALFPOINT_OF_NORTHEAST_ORIGIN]);;

(* Lean: left_origin *)
let C972UE_LEFT_ORIGIN = prove
 (c972mc_stmt [] (c972mc_own 4096 `&1` `&2`),
  MESON_TAC[C972UE_NORTHWEST_OUTER_HALFPOINT; C972MC_LEFT_ORIGIN_OF_NORTHWEST_HALFPOINT]);;

(* Lean: one_corner *)
let C972UE_ONE_CORNER = prove
 (c972mc_stmt [] (c972mc_own 2 `&1` `&1`),
  MESON_TAC[C972UE_NORTHEAST_ORIGIN; C972NH_ONE_CORNER_OF_NORTHEAST_ORIGIN]);;

(* Lean: zero_missing_corner *)
let C972UE_ZERO_MISSING_CORNER = prove
 (c972mc_stmt [] (mk_neg (c972mc_own 1 `&1` `&1`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972UE_ONE_CORNER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&1`; `&1`] (c972mc_apart 1 2)) THEN ASM_REWRITE_TAC[]);;

(* Lean: southeast_missing_halfpoint *)
let C972UE_SOUTHEAST_MISSING_HALFPOINT = prove
 (c972mc_stmt [] (mk_neg (c972mc_own 512 `&3` `&3 / &2`)),
  MESON_TAC[C972UE_ZERO_MISSING_CORNER; C972MC_ZERO_CORNER_OF_SOUTHEAST_HALFPOINT]);;
