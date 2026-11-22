(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualNonordinary.lean               *)
(* (N12Compact.C1092MPPMActualNonordinary; Lean header: "Source only,        *)
(* uncompiled").  Actual residual-elbow ancestry.  Conventions of            *)
(* CP_C1092_MPPMActualPositiveOrder.ml / CP_C1092_MPPMActualWallReduction.ml:*)
(* owners p i at mask EL i c1092wc_code, side l; WallContext p mppm          *)
(* C1092MPPE_CTX; Ordinary / Inward / Elbow of an OpenSquare are             *)
(* c1092mcc_ordinary / c1092mcc_inward / c1092mcc_elbow; g.pullPacking p is  *)
(* (d1,d2,e1,e2) with c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2); the three    *)
(* transforms used, (T,T,F), (F,T,T), (T,F,T), are rotations 1, 2, 3 of      *)
(* MPPMActualPositiveOrder (branchAction g mppm = mppm is                    *)
(* C1092MPAPO_ROTATION_CONTEXT); owners of the pulled packing are rewritten  *)
(* back with c1092mpapo_pull_tac.  An OpenSquare E is cE sE uE vE aE with its*)
(* invariants as hypotheses; (owners p i).translated 2 2 is the tuple of     *)
(* C1092PSA_INSIDE_TRANSLATED.  Used: MPPMElbows.southwest_profile           *)
(* C1092ME_SOUTHWEST_PROFILE, MPPMInwardNeighbors northwest_pair /           *)
(* southeast_pair C1092MIN_NORTHWEST_PAIR / C1092MIN_SOUTHEAST_PAIR,         *)
(* MPPMElbowIsolation.impossible C1092MEI_IMPOSSIBLE, far_impossible         *)
(* C1092MANFR_FAR_IMPOSSIBLE, origin_impossible C1092MANE_ORIGIN_IMPOSSIBLE, *)
(* MPPMOrdinaryWallAdvance.right_far C1092OWA_RIGHT_FAR,                     *)
(* MPPMElbowSuccessor.negative_successor C1092MES_NEGATIVE_SUCCESSOR,        *)
(* MPPMPositiveSeedsActual.missing_halfpoint C1092PSA_MISSING_HALFPOINT,     *)
(* MPPMActualRightNear.corner_halfpoint_of_missing_left_origin               *)
(* C1092MARN_CORNER_HALFPOINT_OF_MISSING_LEFT_ORIGIN, MPPMActualWallReduction*)
(* no_missing / wall_pairs / southwest_cover / left_ordinary C1092MPAWR_ ;   *)
(* MPPMCentralCover.no_omission_cover C1092MCC_NO_OMISSION_COVER.            *)
(* The private side_gt / side_same / mark are OO_SIDE / l = l / oo_seed.     *)
(* Tag C1092MANO_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualWallReduction.ml";;
needs "n12/geometry/CP_C1092_MPPMElbows.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardNeighbors.ml";;
needs "n12/geometry/CP_C1092_MPPMElbowIsolation.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinaryFar.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryWallAdvance.ml";;
needs "n12/geometry/CP_C1092_MPPMElbowSuccessor.ml";;
needs "n12/geometry/CP_C1092_MPPMActualPositiveOrder.ml";;
needs "n12/geometry/CP_C1092_MPPMActualRightNear.ml";;
needs "n12/geometry/CP_C1092_MPPMForwardPositiveDActual.ml";;

(* Lean: side_gt (private) *)
let C1092MANO_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: side_same (private) *)
let C1092MANO_SIDE_SAME = C1092MPAPO_SIDE_SAME;;
(* Lean: mark (private) *)
let C1092MANO_MARK = C1092MPAPO_MARK;;

let C1092MANO_V = C1092MPPE_V;;
let C1092MANO_D4 = c1092mpapo_d4 "";;
let C1092MANO_D5 = C1092MANO_D4 @ [`l:real`];;
let c1092mano_in = c1092mppe_in;;
let C1092MANO_OWN4 = c1092ae_own C1092AE_P 4;;
let C1092MANO_DOWN4 = c1092ae_own "d1 d2 e1 e2 l" 4;;
let C1092MANO_HYPS = Printf.sprintf "%s /\\ %s" C1092AE_HYP C1092MPPE_CTX;;
let C1092MANO_EHYPS = Printf.sprintf "%s /\\ c1092mcc_elbow %s" C1092MANO_HYPS C1092MANO_OWN4;;
let C1092MANO_ROTS = [`(false,false,false)`; `(true,true,false)`; `(false,true,true)`; `(true,false,true)`];;

(* the pulled packing of rotation i with NPACK / IMAGE / context / no omission *)
let c1092mano_rot_tac i =
  c1092mpapo_rot_tac "" i THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" i THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MANO_D5 C1092MPAWR_NO_MISSING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;
let c1092mano_pull i idx = c1092mpapo_pull_tac C1092MANO_D4 (el i C1092MANO_ROTS) idx;;
let c1092mano_dhead c th =
  c1092mpapo_head c th && mem `d1:num->real` (frees (concl th));;
(* a theorem about the pulled packing, pulled back to the original owners *)
let c1092mano_dapply i idx th =
  MP_TAC(SPECL C1092MANO_D5 th) THEN ASM_REWRITE_TAC[] THEN c1092mano_pull i idx;;
let C1092MANO_LIT_TAC =
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV);;
let c1092mano_excl_tac i j x y =
  MP_TAC(SPECL (C1092MANO_V @ [mk_small_numeral i; mk_small_numeral j]) C1092WC_OWNERS_DISJOINT) THEN
  ASM_REWRITE_TAC[ldisj; ARITH] THEN DISCH_THEN(MP_TAC o SPECL [x; y]) THEN ASM_REWRITE_TAC[];;
let c1092mano_cover_cases_tac =
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC);;

(* Lean: successor_ordinary *)
let C1092MANO_SUCCESSOR_ORDINARY = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s /\\ %s" C1092AE_P C1092MANO_EHYPS
    (c1092mano_in 5 "&12 / &5" "&1") (c1092mano_in 5 "&113 / &50" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcc_elbow] o check (c1092mpapo_head `c1092mcc_elbow`)) THEN
  MP_TAC(SPECL C1092MANO_V C1092MPAWR_NO_MISSING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mano_rot_tac 1 THEN
  MP_TAC(SPECL C1092MANO_D5 C1092MCC_NO_OMISSION_COVER) THEN ASM_REWRITE_TAC[] THEN
  c1092mano_cover_cases_tac THENL
   [UNDISCH_TAC (parse_term ("c1092mcc_ordinary " ^ C1092MANO_DOWN4)) THEN
    REWRITE_TAC[c1092mcc_ordinary] THEN c1092mano_pull 1 [4] THEN SIMP_TAC[];
    c1092mano_dapply 1 [7] C1092MIN_NORTHWEST_PAIR THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MP_TAC(SPECL C1092MANO_V C1092ME_SOUTHWEST_PROFILE) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
      [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN STRIP_TAC THEN
    MP_TAC(SPECL C1092MANO_D5 C1092ME_SOUTHWEST_PROFILE) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (parse_term ("c1092mcc_elbow " ^ C1092MANO_DOWN4)) THEN
    REWRITE_TAC[c1092mcc_elbow] THEN c1092mano_pull 1 [4] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL C1092MANO_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aC':real = l`))) THEN
    MATCH_MP_TAC (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`;
                         `cC':real`; `sC':real`; `uC':real`; `vC':real`; `l:real`] C1092MEI_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    C1092MANO_LIT_TAC THEN
    REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`)] THEN
    ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `&4 - (--x + &2) = x + &2`; c1092psa_apart 4 5]]);;

(* Lean: predecessor_ordinary *)
let C1092MANO_PREDECESSOR_ORDINARY = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s /\\ %s" C1092AE_P C1092MANO_EHYPS
    (c1092mano_in 7 "&8 / &5" "&3") (c1092mano_in 7 "&87 / &50" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcc_elbow] o check (c1092mpapo_head `c1092mcc_elbow`)) THEN
  c1092mano_rot_tac 3 THEN
  MP_TAC(SPECL C1092MANO_D5 C1092MCC_NO_OMISSION_COVER) THEN ASM_REWRITE_TAC[] THEN
  c1092mano_cover_cases_tac THENL
   [UNDISCH_TAC (parse_term ("c1092mcc_ordinary " ^ C1092MANO_DOWN4)) THEN
    REWRITE_TAC[c1092mcc_ordinary] THEN c1092mano_pull 3 [4] THEN SIMP_TAC[];
    c1092mano_dapply 3 [5] C1092MIN_SOUTHEAST_PAIR THEN ASM_REWRITE_TAC[];
    c1092mano_dapply 3 [5] C1092MANO_SUCCESSOR_ORDINARY THEN ASM_REWRITE_TAC[]]);;

let C1092MANO_ORD7 = Printf.sprintf "%s /\\ %s" (c1092mano_in 7 "&8 / &5" "&3") (c1092mano_in 7 "&87 / &50" "&3");;

(* Lean: northwest_halfpoint *)
let C1092MANO_NORTHWEST_HALFPOINT = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ (%s) /\\ ~%s ==> %s" C1092AE_P C1092MANO_HYPS C1092MANO_ORD7
    (c1092mano_in 7 "&2" "&113 / &50") (c1092mano_in 7 "&3 / &2" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpapo_rot_tac "" 3 THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 3 THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MANO_D5 C1092PSA_MISSING_HALFPOINT) THEN
  c1092mano_pull 3 [4] THEN ASM_REWRITE_TAC[]);;

(* Lean: left_origin_of_halfpoint *)
let C1092MANO_LEFT_ORIGIN_OF_HALFPOINT = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s" C1092AE_P C1092MANO_HYPS
    (c1092mano_in 7 "&3 / &2" "&3") (c1092mano_in 8 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MPAWR_LEFT_ORDINARY) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MARN_CORNER_HALFPOINT_OF_MISSING_LEFT_ORIGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mano_excl_tac 7 3 `&3 / &2` `&3`);;

let C1092MANO_EV = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;
let C1092MANO_CV = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`];;
let C1092MANO_EVL = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `l:real`];;
let C1092MANO_EACT = "(!x y. linside cE sE uE vE aE x y <=> " ^ c1092mano_in 5 "&2 + x" "&2 + y" ^ ")";;
(* a literal-mask assumption (after C1092MANO_LIT_TAC) *)
let c1092mano_lasm i x y = ASSUME (c1092fpda_lit (c1092mano_in i x y));;

(* C (southwest profile of owner 4) in the assumptions, frame turned to the 2 + x form *)
let C1092MANO_PROFILE_TAC =
  MP_TAC(SPECL C1092MANO_V C1092ME_SOUTHWEST_PROFILE) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[REAL_ARITH `x + &2 = &2 + x`] o
    check (fun th -> is_forall (concl th) && mem `cC:real` (frees (concl th))));;

(* the shared point / face facts of both endings, literal masks *)
let c1092mano_end_facts () =
  [c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
   c1092psa_seed 8 (`&457 / &500`, `&2`);
   c1092psa_excl 5 10 (c1092mano_lasm 10 "&3" "&8 / &5");
   c1092psa_excl 5 1 (c1092psa_seed 1 (`&3`, `&1`));
   c1092psa_excl 5 9 (c1092psa_seed 9 (`&2`, `&457 / &500`));
   c1092psa_apart 4 5; c1092psa_apart 4 8; c1092psa_unit 8; c1092psa_pos (); c1092psa_side ()];;

(* L = (owners p 8).translated 2 2, literal mask *)
let c1092mano_l8 () =
  let o8 = c1092psa_own 8 in
  let [c; s; u; v; _] = o8 in
  let t = SPECL [c; s; u; v; `l:real`; `&2`; `&2`; `x:real`; `y:real`] C1092PSA_INSIDE_TRANSLATED in
  fst (chop_list 5 (snd (strip_comb (lhs (concl t)))));;

(* Lean: impossible_of_negative_successor *)
let C1092MANO_IMPOSSIBLE_OF_NEGATIVE_SUCCESSOR = prove
 (parse_term (Printf.sprintf "!%s cE sE uE vE aE. %s /\\ cE * cE + sE * sE = &1 /\\ &0 < aE /\\ aE = l /\\ %s /\\
      c977cc_normal cE (--sE) ==> F" C1092AE_P C1092MANO_EHYPS C1092MANO_EACT),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = l`)) THEN
  MP_TAC(SPECL C1092MANO_V C1092MPAWR_WALL_PAIRS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MANO_SUCCESSOR_ORDINARY) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MANO_PREDECESSOR_ORDINARY) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MPAWR_NO_MISSING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MANO_PROFILE_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcc_elbow] o check (c1092mpapo_head `c1092mcc_elbow`)) THEN
  (* noF9 *)
  SUBGOAL_THEN (mk_neg (parse_term (c1092mano_in 6 "&3" "&113 / &50"))) ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL C1092MANO_V C1092OWA_RIGHT_FAR) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC (SPECL (C1092MANO_CV @ C1092MANO_EVL @ c1092mano_l8 ()) C1092MANFR_FAR_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN C1092MANO_LIT_TAC THEN
    REWRITE_TAC(c1092psa_excl 5 10 (c1092mano_lasm 10 "&3" "&36 / &25") :: c1092mano_end_facts ()) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* opposite, through rotation 2 *)
  SUBGOAL_THEN (parse_term (c1092mano_in 6 "&2" "&113 / &50" ^ " /\\ " ^ c1092mano_in 6 "&113 / &50" "&2"))
    STRIP_ASSUME_TAC THENL
   [c1092mano_rot_tac 2 THEN
    MP_TAC(SPECL C1092MANO_D5 C1092MPAWR_SOUTHWEST_COVER) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[c1092mcc_ordinary; c1092mcc_inward; c1092mcc_elbow] THEN
    c1092mano_pull 2 [4] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mano_in 7 "&2" "&113 / &50"))) ASSUME_TAC THENL
   [c1092mano_excl_tac 7 6 `&2` `&113 / &50`; ALL_TAC] THEN
  MP_TAC(SPECL C1092MANO_V C1092MANO_NORTHWEST_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MANO_LEFT_ORIGIN_OF_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MANO_CV @ C1092MANO_EVL) C1092MANE_ORIGIN_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[ldisj] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN C1092MANO_LIT_TAC THEN
  REWRITE_TAC(c1092psa_excl 4 8 (c1092mano_lasm 8 "&1" "&2") :: c1092mano_end_facts ()) THEN
  ASM_REWRITE_TAC[]);;

(* E = (owners p 5).translated 2 2, literal mask *)
let c1092mano_e5 () =
  let [c; s; u; v; _] = c1092psa_own 5 in
  let t = SPECL [c; s; u; v; `l:real`; `&2`; `&2`; `x:real`; `y:real`] C1092PSA_INSIDE_TRANSLATED in
  fst (chop_list 5 (snd (strip_comb (lhs (concl t)))));;

(* Lean: impossible *)
let C1092MANO_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s. %s ==> F" C1092AE_P C1092MANO_EHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MANO_SUCCESSOR_ORDINARY) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MPAWR_WALL_PAIRS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MPAWR_NO_MISSING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MANO_PROFILE_TAC THEN
  C1092MANO_LIT_TAC THEN
  MP_TAC(SPECL (C1092MANO_CV @ c1092mano_e5 ()) C1092MES_NEGATIVE_SUCCESSOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC(c1092mano_end_facts ()) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(c1092psa_unit 5) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cF:real`; `sF:real`; `uF:real`; `vF:real`; `aF:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MANO_V @ [`cF:real`; `sF:real`; `uF:real`; `vF:real`; `aF:real`])
    C1092MANO_IMPOSSIBLE_OF_NEGATIVE_SUCCESSOR) THEN
  C1092MANO_LIT_TAC THEN ASM_REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED]);;

(* Lean: ordinary_or_inward *)
let C1092MANO_ORDINARY_OR_INWARD = prove
 (parse_term (Printf.sprintf "!%s. %s ==> c1092mcc_ordinary %s \\/ c1092mcc_inward %s"
    C1092AE_P C1092MANO_HYPS C1092MANO_OWN4 C1092MANO_OWN4),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MANO_V C1092MPAWR_SOUTHWEST_COVER) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  MATCH_MP_TAC (SPECL C1092MANO_V C1092MANO_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* Lean: all_ordinary_or_inward *)
let C1092MANO_ALL_ORDINARY_OR_INWARD = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2 i. %s /\\ i < 4 /\\ %s ==> c1092mcc_ordinary %s \\/ c1092mcc_inward %s"
    C1092AE_P C1092MANO_HYPS c1092mpapo_dpk C1092MANO_DOWN4 C1092MANO_DOWN4),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL C1092MANO_D5 C1092MANO_ORDINARY_OR_INWARD) THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN
    MAP_EVERY EXISTS_TAC (`EL i c1092mpapo_rotation` :: C1092MPAPO_V4) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC (`EL i c1092mpapo_rotation` :: C1092MPAPO_V4) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (SPECL (C1092MANO_V @ C1092MANO_D4 @ [`i:num`]) C1092MPAPO_ROTATION_CONTEXT) THEN
    ASM_REWRITE_TAC[]]);;
