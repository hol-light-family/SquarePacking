(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/TwoFifthsEntrance.lean              *)
(* (N12Compact.C1092MMMPTwoFifthsEntrance).  The original MMMP branch has no *)
(* remaining profile premises.  Conventions of                               *)
(* CP_C1092_MMMP_TwoFifthsEntranceNorthwest.ml / ...Right.ml (owners p i at  *)
(* mask EL i c1092wc_code, side l; WallContext p mmmp is C1092MMPE_CTX; near *)
(* is C1092MSS_NEAR).  southeast_profile C1092MTFES_SOUTHEAST_PROFILE;       *)
(* MMMPNortheastActualSign.exists_positive C1092MNAS_EXISTS_POSITIVE;        *)
(* northwest_profile C1092MTFNP_NORTHWEST_PROFILE; northeast_core            *)
(* C1092MTFEN_NORTHEAST_CORE; UpperThird.upper_third C1092MUT_UPPER_THIRD;   *)
(* C1092TwoFifths.impossible C1092TFEN_IMPOSSIBLE; input_of_profiles         *)
(* C1092MTFER_INPUT_OF_PROFILES ((owners p 10).translated 2 2 is the tuple   *)
(* C1092MTFE_R); ActualProfile WallPoints c1092map_wall,                     *)
(* right_reach_of_missing_near / impossible_of_wall_points /                 *)
(* branch_of_wall_points C1092MAP_*; TopOrigin.point C1092MMTO_POINT;        *)
(* BranchEnding 1 is c1092wsy_ending 1.  Tag C1092MTFE_.                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceNorthwest.ml";;
needs "n12/geometry/CP_C1092_MMMP_UpperThird.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsEnding.ml";;
needs "n12/geometry/CP_C1092_MMMP_ActualProfile.ml";;

let C1092MTFE_R =
  let q f = parse_term (c1092mtfer_q 10 f) in
  let c = q "ooc" and s = q "oos" and u = q "oou" and v = q "oov" in
  [c; s;
   mk_binop `(-):real->real->real` u
     (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c `&2`)
                                      (mk_binop `( * ):real->real->real` s `&2`));
   mk_binop `(-):real->real->real` v
     (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (mk_comb(`(--):real->real`, s)) `&2`)
                                      (mk_binop `( * ):real->real->real` c `&2`));
   `l:real`];;

let C1092MTFE_EV = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
and C1092MTFE_NV = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`]
and C1092MTFE_WV = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;
let C1092MTFE_CLOSE_TAC =
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC; RASM_ARITH_TAC];;
let c1092mtfe_head c th = is_comb (concl th) && fst (strip_comb (concl th)) = c;;

(* Lean: near_impossible *)
let C1092MTFE_NEAR_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s. %s ==> F" C1092AE_P C1092MTFES_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MMPE_V C1092MTFES_SOUTHEAST_PROFILE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cE:real` (X_CHOOSE_THEN `sE:real` (X_CHOOSE_THEN `uE:real`
    (X_CHOOSE_THEN `vE:real` (X_CHOOSE_THEN `aE:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL C1092MMPE_V C1092MNAS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cN:real` (X_CHOOSE_THEN `sN:real` (X_CHOOSE_THEN `uN:real`
    (X_CHOOSE_THEN `vN:real` (X_CHOOSE_THEN `aN:real` ASSUME_TAC))))) THEN
  MP_TAC(SPECL (C1092MMPE_V @ C1092MTFE_EV @ C1092MTFE_NV) C1092MTFNP_NORTHWEST_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cW:real` (X_CHOOSE_THEN `sW:real` (X_CHOOSE_THEN `uW:real`
    (X_CHOOSE_THEN `vW:real` (X_CHOOSE_THEN `aW:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL (C1092MMPE_V @ C1092MTFE_NV) C1092MTFEN_NORTHEAST_CORE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mnas_pos] o check (c1092mtfe_head `c1092mnas_pos`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mtfes_actual] o check (c1092mtfe_head `c1092mtfes_actual`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mtfnp_core] o check (c1092mtfe_head `c1092mtfnp_core`)) THEN
  SUBGOAL_THEN (list_mk_comb(`ldisj`, C1092MTFE_WV @ C1092MTFE_NV)) ASSUME_TAC THENL
   [REWRITE_TAC[ldisj] THEN
    FIRST_X_ASSUM(fun th -> if is_forall (concl th) && is_iff (snd (strip_forall (concl th))) &&
        can (find_term ((=) `uW:real`)) (concl th) then REWRITE_TAC[th] else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_forall (concl th) && is_iff (snd (strip_forall (concl th))) &&
        can (find_term ((=) `uN:real`)) (concl th) then REWRITE_TAC[th] else NO_TAC) THEN
    CONV_TAC C1092MO_CODE_CONV THEN REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (c1092mo_apart 7 6);
    ALL_TAC] THEN
  ASSUME_TAC (c1092mo_side ()) THEN ASSUME_TAC (c1092mo_pos ()) THEN
  MP_TAC(SPECL (C1092MTFE_WV @ C1092MTFE_NV) C1092MUT_UPPER_THIRD) THEN
  ANTS_TAC THENL [C1092MTFE_CLOSE_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MMPE_V @ C1092MTFE_EV @ C1092MTFE_NV) C1092MTFER_INPUT_OF_PROFILES) THEN
  ANTS_TAC THENL [C1092MTFE_CLOSE_TAC; DISCH_TAC] THEN
  MP_TAC(MP (SPECL (C1092MMPE_V @ [`EL 10 c1092wc_code`]) OO_UNIT) (ASSUME C1092MO_NP)) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL (C1092MTFE_EV @ C1092MTFE_NV @ C1092MTFE_R) C1092TFEN_IMPOSSIBLE) THEN
  ANTS_TAC THENL [C1092MTFE_CLOSE_TAC; REWRITE_TAC[]]);;

(* Lean: wall_points *)
let C1092MTFE_WALL_POINTS = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> c1092map_wall %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092map_wall] THEN CONJ_TAC THENL
   [MP_TAC(SPECL C1092MMPE_V C1092MMTO_POINT) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (SPECL C1092MMPE_V C1092MAP_RIGHT_REACH_OF_MISSING_NEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL C1092MMPE_V C1092MTFE_NEAR_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]]);;

(* Lean: family_impossible *)
let C1092MTFE_FAMILY_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> F" C1092AE_P C1092AE_HYP C1092MMPE_CTX),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MMPE_V C1092MAP_IMPOSSIBLE_OF_WALL_POINTS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (SPECL C1092MMPE_V C1092MTFE_WALL_POINTS) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: branch_ending *)
let C1092MTFE_BRANCH_ENDING = prove
 (`c1092wsy_ending 1`,
  MATCH_MP_TAC C1092MAP_BRANCH_OF_WALL_POINTS THEN ACCEPT_TAC C1092MTFE_WALL_POINTS);;
