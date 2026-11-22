(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972SoutheastCentered.lean         *)
(* (namespaces N12Compact.FiniteCases.C972Local and .C972).  A center-owning *)
(* SW square cannot coexist with C972's positive SE residual.  Conventions   *)
(* of CP_FiniteCases_C972SoutheastPositive.ml (A = cA sA uA vA aA, E = cE sE *)
(* uE vE aE with unit normal and positive side explicit; owners p 5 / 6 =    *)
(* owner 256 / 512).  F4SoutheastSignSupports.Data = c983fss_data,           *)
(* positive_u / negative_w = C983FSS_POSITIVE_U / C983FSS_NEGATIVE_W,        *)
(* ABTransverse.strict_bounds = ABT_STRICT_BOUNDS, positive_southeast_       *)
(* alternatives = FC972SS_POSITIVE_SOUTHEAST_ALTERNATIVES,                   *)
(* exists_positive_southeast / southeast_support_profile = C972SP_*.         *)
(* Tag C972SC_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972SoutheastPositive.ml";;

(* add the conclusion of th, its antecedent proved by rewriting with the assumptions and arithmetic *)
let C972SC_LEMMA_TAC th =
  SUBGOAL_THEN (lhand (concl th)) (fun a -> MP_TAC (MP th a)) THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; DISCH_THEN STRIP_ASSUME_TAC];;

(* Lean: C972Local.positive_southeast_center_impossible *)
let C972SC_POSITIVE_SOUTHEAST_CENTER_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cE sE uE vE aE.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &0 < cA /\ abs sA <= cA /\ sE <= cE /\ aA = aE /\
     linside cA sA uA vA aA (-- &1 / &2) (&0) /\
     linside cA sA uA vA aA (&0) (-- &1 / &2) /\
     linside cA sA uA vA aA (&0) (-- &13 / &50) /\
     linside cA sA uA vA aA (&0) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (-- &7 / &20) /\
     linside cE sE uE vE aE (&1) (-- &13 / &50) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     c983fss_data cE sE uE vE aE /\
     ldisj cA sA uA vA aA cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if fst (strip_comb (concl th)) = `c983fss_data` then
    STRIP_ASSUME_TAC (REWRITE_RULE[c983fss_data] th) else NO_TAC) THEN
  C972SC_LEMMA_TAC (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                 `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
            FC972SS_POSITIVE_SOUTHEAST_ALTERNATIVES) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC (REWRITE_RULE[linside] (ASSUME t)))
   [`linside cA sA uA vA aA (&0) (&0)`; `linside cA sA uA vA aA (&0) (-- &13 / &50)`] THENL
   [ASM_CASES_TAC `&0 <= sA` THENL
     [C972SC_LEMMA_TAC (SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `cA:real`; `sA:real`]
                C983FSS_POSITIVE_U) THEN
      RASM_ARITH_TAC;
      C972SC_LEMMA_TAC (SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `cA:real`; `--sA`]
                C983FSS_NEGATIVE_W) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN RASM_ARITH_TAC];
    C972SC_LEMMA_TAC (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `&0`; `&0`; `cE:real`; `sE:real`]
              ABT_STRICT_BOUNDS) THEN
    RASM_ARITH_TAC;
    C972SC_LEMMA_TAC (SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sA`; `cA:real`]
              C983FSS_POSITIVE_U) THEN
    RASM_ARITH_TAC]);;

(* Lean: C972.southwest_center_missing *)
let C972SC_SOUTHWEST_CENTER_MISSING = prove
 (c972sp_stmt [] [] (mk_neg (c972mc_own 256 `&2` `&2`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_FACTS_TAC THEN MP_TAC C972MC_SIDE THEN DISCH_TAC THEN
  C972SP_USE_TAC C972MC_V5 C972SP_EXISTS_POSITIVE_SOUTHEAST THEN
  FIRST_X_ASSUM(fun th -> if is_exists (concl th) then
    X_CHOOSE_THEN `cE:real` (X_CHOOSE_THEN `sE:real` (X_CHOOSE_THEN `uE:real`
      (X_CHOOSE_THEN `vE:real` (X_CHOOSE_THEN `aE:real` STRIP_ASSUME_TAC)))) th else NO_TAC) THEN
  SUBGOAL_THEN `&0 < cE /\ abs sE <= cE` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c977cc_normal cE sE` THEN UNDISCH_TAC `&0 < sE` THEN
    REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_E) C972SP_SOUTHEAST_SUPPORT_PROFILE THEN
  MP_TAC (SPECL (c972ss_tr22 (c972mc_tuple 256)) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ACCEPT_TAC (c972mc_unit 256); MP_TAC C972MC_SIDE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C972SP_A THEN STRIP_TAC THEN
  SUBGOAL_THEN C972SP_ACT_A ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `linside`)) (concl th) &&
                             can (find_term ((=) `uA:real`)) (concl th)
                           then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[C972NF_TRANSLATED]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C972SP_A @ C972SP_E) C972SC_POSITIVE_SOUTHEAST_CENTER_IMPOSSIBLE) THEN
  REWRITE_TAC[ldisj; ASSUME C972SP_ACT_A; ASSUME C972SP_ACT_E] THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[c972mc_apart 256 512] THEN NO_TAC;
         UNDISCH_TAC `c977cc_normal cE sE` THEN REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
         RASM_ARITH_TAC]);;
