(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveOverlap.lean                 *)
(* (N12Compact.C1092MPPMPositiveOverlap; Lean header: "This source is        *)
(* uncompiled").  Literal original Q4 application of CENTERED-POSITIVE-      *)
(* OVERLAP.  Conventions of CP_C1092_MPPMActualPositiveOrder.ml /            *)
(* CP_C1092_MPPMActualNegativeHalfpoint.ml: owners p i at mask               *)
(* EL i c1092wc_code, side l; Ordinary p is c1092mpapo_ordinary; ActualFrame *)
(* p C is c1092psa_frame, OwnerFrame p 4 is c1092fpda_frame .. 4 (OpenSquare *)
(* invariants as hypotheses); C.translated x y is the tuple of               *)
(* C1092PSA_INSIDE_TRANSLATED; rotation 1 via c1092mpapo_rot_tac /           *)
(* c1092mpapo_pull_tac.  Used: MPPMPositiveOverlapLocal Inputs / center_     *)
(* absent (c1092pol_inputs / C1092POL_CENTER_ABSENT), MPPMActualNegative-    *)
(* Halfpoint.southwest_positive_previous_excluded, MPPMPositiveSeedsActual   *)
(* forward_inputs / bottom_origin_of_missing, ClosedFrames.canonical_frame   *)
(* CLF_CANONICAL_FRAME, S12.inside_segment C1092WC_INSIDE_SEGMENT.  The      *)
(* private side_gt / side_same / mark are OO_SIDE / l = l / oo_seed.         *)
(* Tag C1092MPOA_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMPositiveOverlapLocal.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNegativeHalfpoint.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinary.ml";;

(* Lean: side_gt (private) *)
let C1092MPOA_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: side_same (private) *)
let C1092MPOA_SIDE_SAME = C1092MPAPO_SIDE_SAME;;
(* Lean: mark (private) *)
let C1092MPOA_MARK = C1092MPAPO_MARK;;

let C1092MPOA_V = C1092MPPE_V;;
let C1092MPOA_CV = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092MPOA_CT = [`cC:real`; `sC:real`; `uC - (cC * --(&2) + sC * --(&2))`;
                    `vC - (--sC * --(&2) + cC * --(&2))`; `aC:real`];;
let C1092MPOA_CHYPS = "cC * cC + sC * sC = &1 /\\ &0 < aC /\\ c1092psa_frame c1 c2 a b l cC sC uC vC aC";;

(* Lean: owner_frame *)
let C1092MPOA_OWNER_FRAME = prove
 (`forall c1 c2 a b l cC sC uC vC aC. c1092psa_frame c1 c2 a b l cC sC uC vC aC
     ==> c1092fpda_frame c1 c2 a b l 4 cC sC (uC - (cC * --(&2) + sC * --(&2)))
                         (vC - (--sC * --(&2) + cC * --(&2))) aC`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092psa_frame; c1092fpda_frame; C1092PSA_INSIDE_TRANSLATED] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&2 + --(&2) + x = x`]);;

(* Lean: previous_absent *)
let C1092MPOA_PREVIOUS_ABSENT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ %s /\\ c977cc_normal cC sC ==> ~%s"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MPOA_CHYPS (c1092mppe_in 4 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MPOA_V @ C1092MPOA_CT) C1092MANH_SOUTHWEST_POSITIVE_PREVIOUS_EXCLUDED) THEN
  ASM_SIMP_TAC[C1092MPOA_OWNER_FRAME] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: right_origin *)
let C1092MPOA_RIGHT_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 4 "&2" "&87 / &50") (c1092mppe_in 10 "&3" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mppe_in 5 "&2" "&87 / &50"))) ASSUME_TAC THENL
   [c1092mano_excl_tac 5 4 `&2` `&87 / &50`; ALL_TAC] THEN
  c1092manh_rot_ord_tac 1 THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpapo_ordinary] o
    check (fun th -> c1092mpapo_head `c1092mpapo_ordinary` th &&
                     hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
  MP_TAC(SPECL C1092MANH_D5 C1092MPAWR_BOTTOM_ORDINARY) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MANH_D5 C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN ASM_REWRITE_TAC[] THEN
  c1092mpapo_pull_tac (c1092mpapo_d4 "") `(true,true,false)` [4; 9] THEN ASM_REWRITE_TAC[]);;

(* E = (owners p 5).translated 2 2, literal mask *)
let C1092MPOA_Q5 = c1092mano_e5 ();;

(* Lean: original_center_absent *)
let C1092MPOA_ORIGINAL_CENTER_ABSENT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cC sC ==> ~%s"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&2" "&87 / &50")
    C1092MPOA_CHYPS (c1092mppe_in 4 "&2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPOA_V C1092MPAWR_WALL_PAIRS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPOA_V @ C1092MPOA_CV) C1092MPOA_PREVIOUS_ABSENT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MPOA_V C1092MPOA_RIGHT_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MPAPO_ORD_TAC THEN
  MP_TAC(SPECL (C1092MPOA_V @ C1092MPOA_CV) C1092PSA_FORWARD_INPUTS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* short *)
  SUBGOAL_THEN (parse_term (c1092mppe_in 10 "&3" "&161 / &100")) ASSUME_TAC THENL
   [MP_TAC(SPECL
      [parse_term "ooc c1 c2 a b l (EL 10 c1092wc_code)"; parse_term "oos c1 c2 a b l (EL 10 c1092wc_code)";
       parse_term "oou c1 c2 a b l (EL 10 c1092wc_code)"; parse_term "oov c1 c2 a b l (EL 10 c1092wc_code)";
       `l:real`; `&3`; `&8 / &5`; `&3`; `&87 / &50`; `&1 / &14`] C1092WC_INSIDE_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPOA_Q5) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[c1092psa_unit 5; c1092psa_pos ()];
    ALL_TAC] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPOA_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092mpapo_head `c1092psa_frame`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aE:real = l`))) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `l:real`] C1092POL_CENTER_ABSENT) THEN
  ASM_REWRITE_TAC[c1092pol_inputs; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  let la i x y = c1092mano_lasm i x y in
  REWRITE_TAC[c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
    c1092psa_excl 5 10 (la 10 "&3" "&161 / &100");
    c1092psa_excl 5 9 (c1092psa_seed 9 (`&2`, `&457 / &500`));
    c1092psa_excl 5 1 (c1092psa_seed 1 (`&3`, `&1`));
    c1092psa_excl 5 10 (la 10 "&3" "&2");
    c1092psa_excl 5 10 (la 10 "&3" "&8 / &5");
    c1092psa_apart 4 5] THEN
  ASM_REWRITE_TAC[]);;
