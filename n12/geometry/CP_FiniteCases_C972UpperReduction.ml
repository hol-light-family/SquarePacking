(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972UpperReduction.lean            *)
(* (namespace N12Compact.FiniteCases.C972).  Actual-owner reductions above   *)
(* C972's compulsory entrance.  owners p i is the owner of mask              *)
(* EL i c972o_masks, written with the literal mask (owners 0..11 = masks     *)
(* 1,2,12,48,192,256,512,1024,2048,4096,8192,16384).  fixed = C972CS_FIXED,  *)
(* foreign = C972CS_CLASH_TAC / c972mc_excl, apart = oo_apart,               *)
(* FourSquareHighRight.impossible = FSHR_IMPOSSIBLE (Premises = its          *)
(* hypothesis list), OrdinaryMarkerHalfpoint.point_original =                *)
(* OCOMHM_POINT_ORIGINAL, WallProfile.boundary_origin =                      *)
(* OCWPBO_BOUNDARY_ORIGIN, NorthwestSharpPoint.point_original =              *)
(* CCNWS_POINT_ORIGINAL.  The private `close` is LINSIDE_CLOSED.  Tag C972UR_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972MissingCorner.ml";;
needs "n12/geometry/FourSquareHighRight.ml";;
needs "n12/geometry/CP_CommonCases_NorthwestSharpPoint.ml";;

let c972ur_own = c972mc_own and c972ur_tuple = c972mc_tuple and c972ur_stmt = c972mc_stmt;;

(* pulled 5-tuples (pullX, pullY, pullSwap) *)
let c972ur_px t = match t with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`])
                         [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`]
  | _ -> failwith "c972ur_px";;
let c972ur_py t = match t with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`])
                         [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`]
  | _ -> failwith "c972ur_py";;
let c972ur_sw = c983ld_sw;;

let C972UR_OWNERS_TAC ms = MAP_EVERY C972CS_OWNER_TAC ms;;

(* Lean: northeast_not_inward *)
let C972UR_NORTHEAST_NOT_INWARD = prove
 (c972ur_stmt [] (mk_neg (mk_conj(c972ur_own 1024 `&2` `&113 / &50`, c972ur_own 1024 `&113 / &50` `&2`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972CS_FIXED_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHWEST_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C972MC_V5 @ [`&5 / &2`]) C972CS_RIGHT_BAR) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL (oo_inst C972D_F (oo_seed 192 (`&1`, `&1543 / &500`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL OO_SIDE_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  C972UR_OWNERS_TAC [1024; 2048; 4096; 16384] THEN
  MAP_EVERY (fun (m, n) -> C972CS_APART m n) [1024, 2048; 1024, 16384; 2048, 4096; 2048, 16384] THEN
  MAP_EVERY (fun m -> MP_TAC(SPECL (C972MC_V5 @ [mk_small_numeral m]) OO_LSQUARE) THEN
                      ASM_REWRITE_TAC[] THEN DISCH_TAC) [1024; 2048; 4096; 16384] THEN
  MATCH_MP_TAC (SPECL (c972ur_tuple 1024 @ c972ur_tuple 2048 @ c972ur_tuple 4096 @ c972ur_tuple 16384)
                  FSHR_IMPOSSIBLE) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
         MATCH_MP_TAC LINSIDE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C972CS_CLASH_TAC]);;

(* Lean: northeast_halfpoint *)
let C972UR_NORTHEAST_HALFPOINT = prove
 (c972ur_stmt [mk_neg (c972ur_own 1024 `&2` `&113 / &50`)] (c972ur_own 1024 `&5 / &2` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHEAST_G7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHEAST_F7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 1024 THEN
  MATCH_MP_TAC (CONV_RULE C972MC_PULL_CONV
    (SPECL (c972ur_sw (c972ur_px (c972ur_tuple 1024)) @ [`&43 / &500`]) OCOMHM_POINT_ORIGINAL)) THEN
  C972MC_SIDE_TAC []);;

(* Lean: right_origin_of_northeast_halfpoint *)
let C972UR_RIGHT_ORIGIN_OF_NORTHEAST_HALFPOINT =
  let pull t = c972ur_sw (c972ur_py (c972ur_px t)) in
  prove
   (c972ur_stmt [c972ur_own 1024 `&5 / &2` `&3`] (c972ur_own 16384 `&3` `&2`),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 16384 THEN C972CS_OWNER_TAC 48 THEN
    MP_TAC(SPEC_ALL (oo_inst C972D_F (oo_seed 48 (`&1543 / &500`, `&3`)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC (CONV_RULE C972MC_PULL_CONV
      (SPECL (pull (c972ur_tuple 16384) @ pull (c972ur_tuple 48) @ [`&457 / &500`; `&8 / &5`])
         OCWPBO_BOUNDARY_ORIGIN)) THEN
    C972MC_SIDE_TAC
     [C972MC_WALL_TAC 16384; C972MC_WALL_TAC 48;
      REWRITE_TAC[ldisj; LINSIDE_PULLSW; LINSIDE_PULLY; LINSIDE_PULLX] THEN
      MP_TAC (SPEC_ALL (oo_apart C972D_F 48 16384)) THEN ASM_REWRITE_TAC[ldisj] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: northwest_forward_right_origin *)
let C972UR_NORTHWEST_FORWARD_RIGHT_ORIGIN = prove
 (c972ur_stmt [c972ur_own 2048 `&2` `&113 / &50`] (c972ur_own 16384 `&3` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_neg (c972ur_own 1024 `&2` `&113 / &50`)) ASSUME_TAC THENL
   [DISCH_TAC THEN C972CS_CLASH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL C972UR_NORTHEAST_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972UR_RIGHT_ORIGIN_OF_NORTHEAST_HALFPOINT) THEN ASM_REWRITE_TAC[]);;

(* Lean: northwest_missing_sharp *)
let C972UR_NORTHWEST_MISSING_SHARP = prove
 (c972ur_stmt [mk_neg (c972ur_own 2048 `&2` `&113 / &50`)] (c972ur_own 2048 `&13 / &6` `&721 / &300`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972MC_REMAINING_ALTERNATIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHWEST_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 2048 THEN
  MATCH_MP_TAC (SPECL (c972ur_tuple 2048) CCNWS_POINT_ORIGINAL) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C972CS_CLASH_TAC;
         X_GEN_TAC `z:real` THEN REPEAT DISCH_TAC THEN
         MP_TAC(SPECL (C972MC_V5 @ [`z:real`]) C972MC_LEFT_BAR) THEN ASM_REWRITE_TAC[] THEN
         DISCH_TAC THEN C972CS_CLASH_TAC]);;

(* the strict triangle F5, (2,3), NE marker contains the sharp point
   (barycentric weights 603, 211, 740 over 1554) *)
let C972UR_TRIANGLE = prove
 (`forall c s u v a. linside c s u v a (&2) (&113 / &50) /\ linside c s u v a (&2) (&3) /\
     linside c s u v a (&47 / &20) (&47 / &20) ==> linside c s u v a (&13 / &6) (&721 / &300)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: northeast_missing_f5 *)
let C972UR_NORTHEAST_MISSING_F5 = prove
 (c972ur_stmt [] (mk_neg (c972ur_own 1024 `&2` `&113 / &50`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972CS_FIXED_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (c972ur_own 2048 `&2` `&113 / &50`)) ASSUME_TAC THENL
   [DISCH_TAC THEN C972CS_CLASH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL C972MC_REMAINING_ALTERNATIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972UR_NORTHWEST_MISSING_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (c972ur_own 1024 `&13 / &6` `&721 / &300`) ASSUME_TAC THENL
   [MATCH_MP_TAC C972UR_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C972CS_CLASH_TAC);;

(* Lean: northeast_outer_halfpoint *)
let C972UR_NORTHEAST_OUTER_HALFPOINT = prove
 (c972ur_stmt [] (c972ur_own 1024 `&5 / &2` `&3`),
  MESON_TAC[C972UR_NORTHEAST_HALFPOINT; C972UR_NORTHEAST_MISSING_F5]);;

(* Lean: right_origin *)
let C972UR_RIGHT_ORIGIN = prove
 (c972ur_stmt [] (c972ur_own 16384 `&3` `&2`),
  MESON_TAC[C972UR_RIGHT_ORIGIN_OF_NORTHEAST_HALFPOINT; C972UR_NORTHEAST_OUTER_HALFPOINT]);;
