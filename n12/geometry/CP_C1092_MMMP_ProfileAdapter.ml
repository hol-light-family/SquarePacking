(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/ProfileAdapter.lean                 *)
(* (N12Compact.C1092MMMPProfileAdapter).  The exact remaining MMMP           *)
(* obligation: a StrongNortheast profile completes BranchEnding 1.           *)
(* Conventions of CP_C1092_MMMP_PointCore.ml / CP_C1092_MMMP_Origins.ml.     *)
(* The structure StrongNortheast p (a square with its fields) is the         *)
(* predicate c1092mpa_strong c1 c2 a b l cN sN uN vN aN on the five         *)
(* coordinates of `square` (with the OpenSquare invariants unit normal and   *)
(* positive side); C1092MMMPEnding.Profile is c1092mend_profile and          *)
(* C1092MMMPEnding.impossible is C1092MEND_IMPOSSIBLE; (owners p 7).translated*)
(* 2 2 is built with c1092mo_layers.  BranchEnding k is c1092wsy_ending k.   *)
(* Tag C1092MPA_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_PointCore.ml";;
needs "n12/geometry/CP_C1092_MMMP_Ending.ml";;

(* Lean: StrongNortheast (structure; fields side, actual, normal, sine, faces) *)
let c1092mpa_strong = new_definition
 `c1092mpa_strong c1 c2 a b l (cN:real) (sN:real) (uN:real) (vN:real) (aN:real) <=>
    (cN * cN + sN * sN = &1 /\ &0 < aN) /\
    aN = l /\
    (forall x y. linside cN sN uN vN aN x y <=>
           linside (ooc c1 c2 a b l (EL 6 c1092wc_code)) (oos c1 c2 a b l (EL 6 c1092wc_code))
                   (oou c1 c2 a b l (EL 6 c1092wc_code)) (oov c1 c2 a b l (EL 6 c1092wc_code)) l
                   (x + &2) (y + &2)) /\
    c977cc_normal cN sN /\
    &252 / &373 <= sN /\
    c1092mend_profile cN sN uN vN aN`;;

(* Lean: family_impossible *)
let C1092MPA_FAMILY_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cN sN uN vN aN. %s /\\ %s /\\ c1092mpa_strong %s cN sN uN vN aN ==> F"
    C1092AE_P C1092AE_HYP C1092MMPE_CTX C1092AE_P),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mpa_strong] THEN STRIP_TAC THEN
  let tW, eqW = c1092mo_layers 7 [c1092mo_tr `&2` `&2`] in
  let ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR in
  let tip = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MPC_LEFT_TIP)) in
  let facts = [c1092mo_punit 7 tW; c1092mo_pos (); c1092mo_side ();
               c1092mo_use C1092MPC_NORTHWEST_CENTER; c1092mo_use C1092MO_NORTHWEST_LEFT;
               c1092mo_use C1092MPC_NORTHWEST_DIAGONAL;
               c1092mo_seed 7 (`&33 / &20`, `&47 / &20`);
               c1092mo_excl 7 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`));
               c1092mo_excl 7 8 tip;
               c1092mo_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT1 ne; CONJUNCT2 ne;
               c1092mo_apart 7 6] in
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) && is_iff (snd (strip_forall (concl th))) &&
      (match strip_comb (lhs (snd (strip_forall (concl th)))) with (_, args) -> el 0 args = `cN:real`)
    then ASSUME_TAC (REWRITE_RULE[REAL_ARITH `forall x. x + &2 = &2 + x`] (CONV_RULE C1092MO_CODE_CONV th))
    else NO_TAC) THEN
  MATCH_MP_TAC (SPECL (tW @ [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`]) C1092MEND_IMPOSSIBLE) THEN
  REWRITE_TAC[ldisj] THEN CONV_TAC (c1092mo_conv eqW) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM (ACCEPT_TAC o SYM);
         REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

(* Lean: action (local fact of branch_of_profile) *)
let C1092MPA_ACTION = prove
 (`forall k. k < 4 ==> c1092ws_branch_action (false,false,true) (c1092ws_canonical_branch 1) k = c1092mmpe_mmmp k`,
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN CONV_TAC c1092ae_act_conv THEN
  REWRITE_TAC[c1092ws_canonical_branch; c1092mmpe_mmmp] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Lean: branch_of_profile *)
let C1092MPA_BRANCH_OF_PROFILE = prove
 (parse_term (Printf.sprintf
   "(!%s. %s /\\ %s ==> ?cN sN uN vN aN. c1092mpa_strong %s cN sN uN vN aN) ==> c1092wsy_ending 1"
   C1092AE_P C1092AE_HYP C1092MMPE_CTX C1092AE_P),
  let g = `(false,false,true)` and v4 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
  DISCH_TAC THEN REWRITE_TAC[c1092wsy_ending] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exists d1 d2 e1 e2. c1092ot_pk (false,false,true) (c1,c2,a,b) = (d1,d2,e1,e2)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `NPACK d1 d2 e1 e2 l` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: v4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1092wc_ctx d1 d2 e1 e2 l c1092mmpe_mmmp` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092MMEN_CTX_CONG THEN
    EXISTS_TAC `c1092ws_branch_action (false,false,true) (c1092ws_canonical_branch 1)` THEN
    REWRITE_TAC[C1092MPA_ACTION] THEN
    MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN MAP_EVERY EXISTS_TAC v4 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`;
                       `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] C1092MPA_FAMILY_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;
