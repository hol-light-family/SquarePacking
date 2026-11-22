(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/ActualProfile.lean                  *)
(* (N12Compact.C1092MMMPActualProfile).  The strong northeast profile        *)
(* reduces to two strict points of named original wall owners (WallPoints,  *)
(* an explicit premise: "this is not a completed branch").  Conventions of   *)
(* CP_C1092_MMMP_ProfileAdapter.ml (StrongNortheast is c1092mpa_strong,      *)
(* family_impossible C1092MPA_FAMILY_IMPOSSIBLE, branch_of_profile           *)
(* C1092MPA_BRANCH_OF_PROFILE, BranchEnding 1 is c1092wsy_ending 1) and      *)
(* CP_C1092_MMMP_NortheastActualSign.ml (PositiveActual is c1092mnas_pos).   *)
(* StrongNortheastFaces.profile C1092MSNF_PROFILE; WallLowerReach.point      *)
(* WLR_POINT; boundary_origin via c1092mo_origin; RightFar.point             *)
(* C1092MRF_POINT; right_missing_inner C1092MRIA_RIGHT_MISSING_INNER;        *)
(* OriginalOwners.vertical_segment OO_VERTICAL_SEGMENT.  The Lean noncomputable *)
(* def strong_northeast is the existence theorem C1092MAP_STRONG_NORTHEAST.  *)
(* Tag C1092MAP_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_NortheastActualSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_StrongNortheastFaces.ml";;
needs "n12/geometry/CP_C1092_MMMP_ProfileAdapter.ml";;
needs "n12/geometry/CP_C1092_MMMP_RightFar.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: WallPoints *)
let c1092map_wall = new_definition
 (parse_term (Printf.sprintf "c1092map_wall (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=> %s /\\ %s"
    (c1092mmpe_in 11 "&2" "&3") (c1092mmpe_in 10 "&3" "&64 / &25")));;

let c1092map_stmt hyps concl =
  parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P (String.concat " /\\ " ([C1092AE_HYP; C1092MMPE_CTX] @ hyps)) concl);;

(* Lean: right_reach_of_missing_near *)
let C1092MAP_RIGHT_REACH_OF_MISSING_NEAR = prove
 (c1092map_stmt ["~" ^ C1092MSS_NEAR] (c1092mmpe_in 10 "&3" "&64 / &25"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MRF_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MRIA_RIGHT_MISSING_INNER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let a i x y = ASSUME (c1092mo_in i x y) in
  let t, eqs = c1092mo_layers 10 [C1092MO_X] in
  ACCEPT_TAC (c1092mo_apply (c1092mo_conv eqs) (SPECL t WLR_POINT)
    [c1092mo_punit 10 t; c1092mo_side (); c1092mo_plcont 10 [C1092MO_X];
     c1092mo_seed 10 (`&1543 / &500`, `&2`); a 10 `&3` `&12 / &5`;
     ASSUME (mk_neg (c1092mo_in 10 `&3` `&87 / &50`));
     ASSUME (mk_neg (c1092mo_in 10 `&113 / &50` `&2`))]));;

let C1092MAP_HALF = c1092mmpe_in 8 "&1" "&5 / &2";;

(* Lean: top_origin_of_left_halfpoint *)
let C1092MAP_TOP_ORIGIN_OF_LEFT_HALFPOINT = prove
 (c1092map_stmt [C1092MAP_HALF] (c1092mmpe_in 11 "&2" "&3"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let top = c1092mo_use C1092MMPE_TOP_PAIR in
  let half = ASSUME (c1092mo_in 8 `&1` `&5 / &2`) in
  ACCEPT_TAC (c1092mo_origin [C1092MO_Y] 11 3 `&457 / &500` `&8 / &5`
    [c1092mo_seed 11 (`&2`, `&1543 / &500`); CONJUNCT1 top;
     c1092mo_seed 3 (`&1`, `&1543 / &500`); c1092mo_seed 3 (`&1`, `&3`);
     c1092mo_excl 3 8 half]
    [`x:real`; `&4 - y`]));;

(* Lean: wall_points_of_entrance *)
let C1092MAP_WALL_POINTS_OF_ENTRANCE = prove
 (c1092map_stmt [C1092MAP_HALF; "~" ^ C1092MSS_NEAR] "c1092map_wall c1 c2 a b l",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092map_wall] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C1092MAP_TOP_ORIGIN_OF_LEFT_HALFPOINT;
    MATCH_MP_TAC C1092MAP_RIGHT_REACH_OF_MISSING_NEAR] THEN ASM_REWRITE_TAC[]);;

(* Lean: strong_northeast (noncomputable def; here the existence of the structure) *)
let C1092MAP_STRONG_NORTHEAST = prove
 (c1092map_stmt ["c1092map_wall c1 c2 a b l"] "?cN sN uN vN aN. c1092mpa_strong c1 c2 a b l cN sN uN vN aN",
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092map_wall] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MNAS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[c1092mnas_pos] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  MAP_EVERY EXISTS_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `l:real`] THEN
  REWRITE_TAC[c1092mpa_strong] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ADD_SYM]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC C1092MSNF_PROFILE THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  let a i x y = ASSUME (c1092mo_in i x y) in
  let ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR and nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  let inner = CONV_RULE REAL_RAT_REDUCE_CONV (MATCH_MP C1092WC_INSIDE_SEGMENT
    (end_itlist CONJ [c1092mo_use C1092MPC_NORTHWEST_CENTER; c1092mo_use C1092MPC_NORTHWEST_NORTH;
                      REAL_ARITH `&0 <= &4 / &5`; REAL_ARITH `&4 / &5 <= &1`])) in
  let hy = `&13 / &50 <= y` and hu = `y <= &14 / &25` in
  let bar = MATCH_MP OO_VERTICAL_SEGMENT (end_itlist CONJ
    [CONJUNCT1 (CONJUNCT2 (CONJUNCT2 wa)); a 10 `&3` `&64 / &25`;
     REAL_ARITH `&113 / &50 < &64 / &25`;
     MP (REAL_ARITH (mk_imp(hy, `&113 / &50 <= &2 + y`))) (ASSUME hy);
     MP (REAL_ARITH (mk_imp(hu, `&2 + y <= &64 / &25`))) (ASSUME hu)]) in
  let rbar = GEN `y:real` (DISCH hy (DISCH hu (c1092mo_excl 6 10 bar))) in
  ASM_REWRITE_TAC[CONJUNCT2 ne; c1092mo_seed 6 (`&47 / &20`, `&47 / &20`);
    c1092mo_excl 6 7 (CONJUNCT1 nw); c1092mo_excl 6 7 inner;
    c1092mo_excl 6 11 (a 11 `&2` `&3`); c1092mo_excl 6 2 (c1092mo_seed 2 (`&3`, `&3`))] THEN
  REPEAT CONJ_TAC THEN
  FIRST [ACCEPT_TAC rbar; MP_TAC(c1092mo_side ()) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Lean: impossible_of_wall_points *)
let C1092MAP_IMPOSSIBLE_OF_WALL_POINTS = prove
 (c1092map_stmt ["c1092map_wall c1 c2 a b l"] "F",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MAP_STRONG_NORTHEAST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] C1092MPA_FAMILY_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: branch_of_wall_points *)
let C1092MAP_BRANCH_OF_WALL_POINTS = prove
 (mk_imp(c1092map_stmt [] "c1092map_wall c1 c2 a b l", `c1092wsy_ending 1`),
  DISCH_TAC THEN MATCH_MP_TAC C1092MPA_BRANCH_OF_PROFILE THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1092MAP_STRONG_NORTHEAST THEN
  ASM_SIMP_TAC[]);;
