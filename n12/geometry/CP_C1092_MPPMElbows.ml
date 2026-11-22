(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMElbows.lean                          *)
(* (N12Compact.C1092MPPMElbows).  Literal residual-elbow profile in its      *)
(* actual southwest owner.  Conventions of CP_C1092_MPPMCentralCover.ml      *)
(* (Elbow is c1092mcc_elbow; owners p i at mask EL i c1092wc_code, side l;   *)
(* forward toolkit c1092mo_ functions).  translate q 2 2 is the explicit tuple  *)
(* (c, s, u - (2c + 2s), v - (2c - 2s), a) (C1092ME_INSIDE_TRANSLATE).       *)
(* C1092ElbowProfile.Profile / exists_profile: c1092ep_profile /             *)
(* C1092EP_EXISTS_PROFILE.  An OpenSquare C is cC sC uC vC aC with its       *)
(* invariants stated explicitly.  Tag C1092ME_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMCentralCover.ml";;
needs "n12/geometry/CP_C1092_ElbowProfile.ml";;

(* Lean: marker_point (private): markers are oo_seed points (c1092mo_seed) *)

(* S12 inside_translate at (2, 2) *)
let C1092ME_INSIDE_TRANSLATE = prove
 (`forall c s u v a x y.
     linside c s (u - (&2 * c + &2 * s)) (v - (&2 * c - &2 * s)) a x y <=>
     linside c s u v a (x + &2) (y + &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: southwest_profile *)
let C1092ME_SOUTHWEST_PROFILE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ (!k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k) /\\
      c1092mcc_elbow %s
      ==> ?cC sC uC vC aC. cC * cC + sC * sC = &1 /\\ &0 < aC /\\ aC = l /\\
            (!x y. linside cC sC uC vC aC x y <=> linside %s (x + &2) (y + &2)) /\\
            c1092ep_profile cC sC uC vC aC"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MOM_ORDINARY_WALLS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcc_elbow] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c1092mcc_elbow`)) THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let [c; s; u; v; a] = c1092mo_own 4 in
  let tA = [c; s; mk_binop `(-):real->real->real` u (mk_binop `(+):real->real->real`
                    (mk_binop `( * ):real->real->real` `&2` c) (mk_binop `( * ):real->real->real` `&2` s));
            mk_binop `(-):real->real->real` v (mk_binop `(-):real->real->real`
                    (mk_binop `( * ):real->real->real` `&2` c) (mk_binop `( * ):real->real->real` `&2` s)); a] in
  MP_TAC(SPECL tA C1092EP_EXISTS_PROFILE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[C1092ME_INSIDE_TRANSLATE; c1092mo_unit 4; c1092mo_pos (); c1092mo_side ()] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[c1092mo_seed 4 (`&33 / &20`, `&33 / &20`);
      c1092mo_excl 4 7 (c1092mo_seed 7 (`&33 / &20`, `&47 / &20`));
      c1092mo_excl 4 8 (c1092mo_seed 8 (`&457 / &500`, `&2`));
      c1092mo_excl 4 9 (ASSUME (c1092mo_in 9 `&8 / &5` `&1`))];
    ALL_TAC] THEN
  REWRITE_TAC[C1092ME_INSIDE_TRANSLATE] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[c1092ep_profile; c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c1092ep_profile c s u v a`) (concl th))) THEN
  MP_TAC(c1092mo_pos ()) THEN REAL_ARITH_TAC);;
