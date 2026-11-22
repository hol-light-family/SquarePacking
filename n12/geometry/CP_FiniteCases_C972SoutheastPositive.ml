(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972SoutheastPositive.lean         *)
(* (namespace N12Compact.FiniteCases.C972).  The missing-SE-halfpoint branch *)
(* of C972 has a strictly positive SE canonical frame.  owners p i = owner   *)
(* of mask EL i c972o_masks, written with the literal mask (owners 5 / 6 /   *)
(* 11 = masks 256 / 512 / 16384).  Lean OpenSquares A, E are cA sA uA vA aA, *)
(* cE sE uE vE aE with unit normal and positive side explicit; Normal =      *)
(* c977cc_normal; lower / upper = ABT_lower / ABT_upper.  Used:             *)
(* C972Local.negative_point = FC972SNH_NEGATIVE_POINT,                       *)
(* C972Local.positive_southeast_alternatives =                              *)
(* FC972SS_POSITIVE_SOUTHEAST_ALTERNATIVES, F4SoutheastSign.entrance =       *)
(* C983FSG_ENTRANCE (Data = c983fss_data), ClosedFrames.canonical_frame =    *)
(* CLF_CANONICAL_FRAME, southeast_g6_of_missing_halfpoint = C972SR_*,       *)
(* fixed / southeast_g8 / southwest_south / southwest_west = C972CS_*,       *)
(* right_origin = C972UR_RIGHT_ORIGIN, foreign / apart = C972CS_CLASH_TAC /  *)
(* c972mc_apart.  Tag C972SP_.                                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972SoutheastSupport.ml";;
needs "n12/geometry/CP_FiniteCases_C972SoutheastNegativeHalfpoint.ml";;
needs "n12/geometry/CP_FiniteCases_C972SoutheastSeparation.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4SoutheastSign.ml";;

let C972SP_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;
let C972SP_A = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`];;
let C972SP_MISSING = mk_neg (c972mc_own 512 `&3` `&3 / &2`);;
let c972sp_actual vs m =
  match vs with [c; s; u; v; a] ->
    let x = `x:real` and y = `y:real` in
    list_mk_forall([x; y], mk_iff(list_mk_comb(`linside`, vs @ [x; y]),
      c972mc_own m (mk_binop `(+):real->real->real` `&2` x) (mk_binop `(+):real->real->real` `&2` y)))
  | _ -> failwith "c972sp_actual";;
let C972SP_ACT_E = c972sp_actual C972SP_E 512 and C972SP_ACT_A = c972sp_actual C972SP_A 256;;
let C972SP_SQ_E = [`cE * cE + sE * sE = &1`; `&0 < aE`; `aE:real = l`; C972SP_ACT_E];;
let C972SP_SQ_A = [`cA * cA + sA * sA = &1`; `&0 < aA`; `aA:real = l`; C972SP_ACT_A];;
let c972sp_stmt vars hyps body =
  list_mk_forall(C972MC_V5 @ vars, mk_imp(list_mk_conj([C972MC_NP; C972MC_IMG; C972SP_MISSING] @ hyps), body));;

(* add the conclusion of th at vars; its antecedent conjuncts must be assumptions *)
let C972SP_USE_TAC vars th (asl, w as g) =
  let th1 = SPECL vars th in
  let get t = try find (fun a -> aconv (concl a) t) (map snd asl)
              with Failure _ -> failwith ("C972SP_USE_TAC: " ^ string_of_term t) in
  ASSUME_TAC (MP th1 (end_itlist CONJ (map get (conjuncts (lhand (concl th1)))))) g;;

(* the retained actual facts of the SE / SW owners as assumptions *)
let C972SP_FACTS_TAC =
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC)
    [C972SR_SOUTHEAST_G6_OF_MISSING_HALFPOINT; C972CS_SOUTHEAST_G8; C972UR_RIGHT_ORIGIN;
     C972CS_SOUTHWEST_SOUTH; C972CS_SOUTHWEST_WEST] THEN
  C972CS_FIXED_TAC;;

(* instantiate a local lemma, rewrite E / A points to owner points, discharge *)
let C972SP_APPLY_TAC acts th =
  MP_TAC th THEN REWRITE_TAC([ldisj] @ map ASSUME acts) THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           REWRITE_TAC[REAL_NEG_NEG] THEN NO_TAC;
           REWRITE_TAC[c972mc_apart 256 512] THEN NO_TAC;
           DISCH_TAC THEN C972CS_CLASH_TAC;
           RASM_ARITH_TAC];
    ALL_TAC];;

(* the lemma's conclusion (sides possibly rewritten to l) implies the goal *)
let C972SP_CLOSE_TAC =
  DISCH_TAC THEN REPEAT (FIRST_X_ASSUM (fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
      rhs (concl th) = `l:real` then SUBST_ALL_TAC th else NO_TAC)) THEN
  FIRST_ASSUM ACCEPT_TAC;;

(* Lean: southeast_positive *)
let C972SP_SOUTHEAST_POSITIVE = prove
 (c972sp_stmt C972SP_E (C972SP_SQ_E @ [`&0 < cE`; `abs sE <= cE`]) `&0 < sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_FACTS_TAC THEN MP_TAC C972MC_SIDE THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c977cc_normal cE (--sE)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN
    UNDISCH_TAC `cE * cE + sE * sE = &1` THEN UNDISCH_TAC `abs sE <= cE` THEN
    UNDISCH_TAC `sE <= &0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC C972SP_MISSING THEN REWRITE_TAC[] THEN
  C972SP_APPLY_TAC [C972SP_ACT_E] (SPECL (C972SP_E @ [`--sE`]) FC972SNH_NEGATIVE_POINT) THEN
  DISCH_THEN ACCEPT_TAC);;

(* Lean: exists_positive_southeast *)
let C972SP_EXISTS_POSITIVE_SOUTHEAST = prove
 (c972sp_stmt [] []
    (list_mk_exists(C972SP_E, list_mk_conj (C972SP_SQ_E @ [`c977cc_normal cE sE`; `&0 < sE`]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL (c972ss_tr22 (c972mc_tuple 512)) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ACCEPT_TAC (c972mc_unit 512); MP_TAC C972MC_SIDE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C972SP_E THEN STRIP_TAC THEN
  SUBGOAL_THEN C972SP_ACT_E ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `linside`)) (concl th)
                           then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[C972NF_TRANSLATED]; ALL_TAC] THEN
  SUBGOAL_THEN `aE:real = l` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_E) C972SP_SOUTHEAST_POSITIVE THEN
  MAP_EVERY EXISTS_TAC C972SP_E THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC]);;

(* Lean: southeast_support_profile *)
let C972SP_SOUTHEAST_SUPPORT_PROFILE = prove
 (c972sp_stmt C972SP_E (C972SP_SQ_E @ [`&0 < cE`; `abs sE <= cE`])
    (list_mk_comb(`c983fss_data`, C972SP_E)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_E) C972SP_SOUTHEAST_POSITIVE THEN
  C972SP_FACTS_TAC THEN MP_TAC C972MC_SIDE THEN DISCH_TAC THEN
  C972SP_APPLY_TAC [C972SP_ACT_E] (SPECL C972SP_E C983FSG_ENTRANCE) THEN
  C972SP_CLOSE_TAC);;

let C972SP_PAIR_HYPS =
  C972SP_SQ_A @ [`&0 < cA`; `abs sA <= cA`] @ C972SP_SQ_E @ [`&0 < cE`; `abs sE <= cE`];;

(* Lean: southeast_pair_alternatives *)
let C972SP_SOUTHEAST_PAIR_ALTERNATIVES = prove
 (c972sp_stmt (C972SP_A @ C972SP_E) C972SP_PAIR_HYPS
    `uA + aA <= ABT_lower cE sE uE vE aE cA sA \/
     ABT_upper cA sA uA vA aA cE sE <= uE \/
     (&17 * sA < -- &7 * cA /\ vA + aA <= ABT_lower cE sE uE vE aE (--sA) cA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_E) C972SP_SOUTHEAST_POSITIVE THEN
  C972SP_FACTS_TAC THEN MP_TAC C972MC_SIDE THEN DISCH_TAC THEN
  C972SP_APPLY_TAC [C972SP_ACT_A; C972SP_ACT_E]
    (SPECL (C972SP_A @ C972SP_E) FC972SS_POSITIVE_SOUTHEAST_ALTERNATIVES) THEN
  C972SP_CLOSE_TAC);;

(* Lean: southeast_nonnegative_pair_alternatives *)
let C972SP_SOUTHEAST_NONNEGATIVE_PAIR_ALTERNATIVES = prove
 (c972sp_stmt (C972SP_A @ C972SP_E)
    (C972SP_SQ_A @ [`&0 < cA`; `&0 <= sA`; `abs sA <= cA`] @ C972SP_SQ_E @ [`&0 < cE`; `abs sE <= cE`])
    `uA + aA <= ABT_lower cE sE uE vE aE cA sA \/ ABT_upper cA sA uA vA aA cE sE <= uE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_A @ C972SP_E) C972SP_SOUTHEAST_PAIR_ALTERNATIVES THEN
  SUBGOAL_THEN `~(&17 * sA < -- &7 * cA)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;
