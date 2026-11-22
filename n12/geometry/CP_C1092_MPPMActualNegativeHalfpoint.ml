(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualNegativeHalfpoint.lean         *)
(* (N12Compact.C1092MPPMActualNegativeHalfpoint; Lean header: "Source only,  *)
(* uncompiled").  ORDINARY-NEGATIVE-HALFPOINT Corollary 2 on the original    *)
(* MPPM owners.  Conventions of CP_C1092_MPPMActualPositiveOrder.ml:         *)
(* owners p i at mask EL i c1092wc_code, side l; WallContext p mppm          *)
(* C1092MPPE_CTX; Ordinary p is c1092mpapo_ordinary; OwnerFrame p i J is     *)
(* c1092fpda_frame .. i J (J's OpenSquare invariants as hypotheses);         *)
(* (rotation i).pullPacking p is (d1,d2,e1,e2) with                          *)
(* c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) (c1092mpapo_rot_tac), owners    *)
(* rewritten back with c1092mpapo_pull_tac.  The frame                       *)
(* turnFrame^3 (g.pull F) of rotation 3 is the explicit 5-tuple              *)
(* (cF, sF, &4 * cF - vF - aF, uF - &4 * sF, aF) (C1092MANH_FRAME_ROT3).     *)
(* J.translated 2 2 is the tuple of C1092PSA_INSIDE_TRANSLATED.  Used:       *)
(* MPPMPositiveSeedsActual missing_halfpoint / exists_canonical_frame /      *)
(* missing_inputs / bottom_origin_of_halfpoint (C1092PSA_ thms),               *)
(* MPPMNonpositivePredecessor Inputs / point (c1092nppt_inputs /             *)
(* C1092NPPT_POINT), MPPMForwardPositiveDActual NonpositiveHalfpoint /       *)
(* southeast_of_nonpositive_halfpoint (C1092FPDA_ thms).The private side_gt /  *)
(* side_same / mark are OO_SIDE / l = l / oo_seed.  Tag C1092MANH_.          *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualPositiveOrder.ml";;
needs "n12/geometry/CP_C1092_MPPMForwardPositiveDActual.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessor.ml";;

(* Lean: side_gt (private) *)
let C1092MANH_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: side_same (private) *)
let C1092MANH_SIDE_SAME = C1092MPAPO_SIDE_SAME;;
(* Lean: mark (private) *)
let C1092MANH_MARK = C1092MPAPO_MARK;;

let C1092MANH_V = C1092MPPE_V;;
let c1092manh_in = c1092mppe_in;;
let C1092MANH_D5 = c1092mpapo_d4 "" @ [`l:real`];;

(* the pulled packing of rotation i with NPACK / IMAGE / context / Ordinary *)
let c1092manh_rot_tac i =
  c1092mpapo_rot_tac "" i THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" i THEN DISCH_TAC;;
let c1092manh_rot_ord_tac i =
  c1092manh_rot_tac i THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" i THEN DISCH_TAC;;

let C1092MANH_STRIP_FRAMES_TAC =
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092fpda_frame; c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092fpda_frame` th || c1092mpapo_head `c1092psa_frame` th)));;

(* Lean: southeast_of_missing *)
let C1092MANH_SOUTHEAST_OF_MISSING = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ ~%s ==> %s" C1092AE_P C1092MPAPO_HYPS
    (c1092manh_in 5 "&2" "&87 / &50") (c1092manh_in 5 "&5 / &2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  c1092manh_rot_tac 1 THEN
  MP_TAC(SPECL C1092MANH_D5 C1092PSA_MISSING_HALFPOINT) THEN
  c1092mpapo_pull_tac (c1092mpapo_d4 "") `(true,true,false)` [4] THEN ASM_REWRITE_TAC[]);;

let C1092MANH_SQJ = "cJ * cJ + sJ * sJ = &1 /\\ &0 < aJ";;
let C1092MANH_FRJ = "c1092fpda_frame c1 c2 a b l 5 cJ sJ uJ vJ aJ";;
let C1092MANH_SQF = "cF * cF + sF * sF = &1 /\\ &0 < aF";;
let C1092MANH_FRF = "c1092fpda_frame c1 c2 a b l 4 cF sF uF vF aF";;

(* Lean: southeast *)
let C1092MANH_SOUTHEAST = prove
 (parse_term (Printf.sprintf "!%s cJ sJ uJ vJ aJ. %s /\\ %s /\\ %s /\\ &0 < cJ /\\ sJ <= &0 /\\ --sJ <= cJ ==> %s"
    C1092AE_P C1092MPAPO_HYPS C1092MANH_SQJ C1092MANH_FRJ (c1092manh_in 5 "&5 / &2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term (c1092manh_in 5 "&2" "&87 / &50")) THENL
   [ALL_TAC;
    MATCH_MP_TAC (SPECL C1092MANH_V C1092MANH_SOUTHEAST_OF_MISSING) THEN ASM_REWRITE_TAC[]] THEN
  C1092MPAPO_ORD_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MANH_V C1092PSA_EXISTS_CANONICAL_FRAME) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN STRIP_TAC THEN
  (* Inputs.missing, proved while the frame of C is still folded *)
  SUBGOAL_THEN (parse_term (Printf.sprintf "~%s ==> c1092mmpf_inputs cC sC uC vC aC"
      (c1092manh_in 4 "&87 / &50" "&2"))) ASSUME_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC (SPECL (C1092MANH_V @ C1092MPAPO_CV) C1092PSA_MISSING_INPUTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL C1092MANH_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MANH_STRIP_FRAMES_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aJ:real = l`))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`;
                `cJ:real`; `sJ:real`; `uJ - (cJ * &2 + sJ * &2)`; `vJ - (--sJ * &2 + cJ * &2)`; `l:real`]
    C1092NPPT_POINT) THEN
  ASM_REWRITE_TAC[c1092nppt_inputs; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  let wa = c1092psa_wa () in
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
    c1092psa_excl 4 0 (c1092psa_seed 0 (`&1`, `&1`));
    c1092psa_excl 4 8 (c1092psa_seed 8 (`&457 / &500`, `&2`));
    c1092psa_excl 4 7 (c1092psa_seed 7 (`&33 / &20`, `&47 / &20`));
    c1092psa_excl 4 8 (CONJUNCT1 wa)] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(REPEAT GEN_TAC THEN REWRITE_TAC[c1092psa_apart 4 5] THEN NO_TAC) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    REWRITE_TAC[]]);;

(* the rotation-3 frame: turnFrame^3 (g.pull F) is an OwnerFrame of owner 5 of the pulled packing *)
let C1092MANH_FRAME_ROT3 = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2 cF sF uF vF aF. %s /\\ c1092ot_pk (T,F,T) (c1,c2,a,b) = (d1,d2,e1,e2) /\\ %s
      ==> c1092fpda_frame d1 d2 e1 e2 l 5 cF sF (&4 * cF - vF - aF) (uF - &4 * sF) aF"
    C1092AE_P C1092AE_HYP C1092MANH_FRF),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[c1092fpda_frame] THEN
  c1092mpapo_pull_tac (c1092mpapo_d4 "") `(true,false,true)` [5] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092fpda_frame] o check (c1092mpapo_head `c1092fpda_frame`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1092MANH_FHYPS = Printf.sprintf "%s /\\ %s /\\ %s" C1092MPAPO_HYPS C1092MANH_SQF C1092MANH_FRF;;
let C1092MANH_FV = [`cF:real`; `sF:real`; `uF:real`; `vF:real`; `aF:real`];;
let C1092MANH_JROT3 = [`cF:real`; `sF:real`; `&4 * cF - vF - aF`; `uF - &4 * sF`; `aF:real`];;

(* rotation 3 with the frame of owner 5 of the pulled packing in the assumptions *)
let C1092MANH_ROT3_TAC =
  c1092manh_rot_ord_tac 3 THEN
  MP_TAC(SPECL (C1092MANH_V @ c1092mpapo_d4 "" @ C1092MANH_FV) C1092MANH_FRAME_ROT3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* Lean: southwest *)
let C1092MANH_SOUTHWEST = prove
 (parse_term (Printf.sprintf "!%s cF sF uF vF aF. %s /\\ &0 < cF /\\ abs sF <= cF /\\ sF <= &0 ==> %s"
    C1092AE_P C1092MANH_FHYPS (c1092manh_in 4 "&1" "&3 / &2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MANH_ROT3_TAC THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MANH_JROT3) C1092MANH_SOUTHEAST) THEN
  c1092mpapo_pull_tac (c1092mpapo_d4 "") `(true,false,true)` [5] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `abs sF <= cF` THEN UNDISCH_TAC `sF <= &0` THEN UNDISCH_TAC `&0 < cF` THEN
  REAL_ARITH_TAC);;

(* Lean: nonpositive_halfpoint *)
let C1092MANH_NONPOSITIVE_HALFPOINT = prove
 (parse_term (Printf.sprintf "!%s. %s ==> c1092fpda_nonpositiveHalfpoint %s"
    C1092AE_P C1092MPAPO_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092fpda_nonpositiveHalfpoint] THEN
  MAP_EVERY X_GEN_TAC C1092MANH_FV THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MANH_V @ C1092MANH_FV) C1092MANH_SOUTHWEST) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: bottom_origin *)
let C1092MANH_BOTTOM_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s cF sF uF vF aF. %s /\\ &0 < cF /\\ abs sF <= cF /\\ sF <= &0 ==> %s"
    C1092AE_P C1092MANH_FHYPS (c1092manh_in 9 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL C1092MANH_V C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (SPECL (C1092MANH_V @ C1092MANH_FV) C1092MANH_SOUTHWEST) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: southeast_positive_previous_excluded *)
let C1092MANH_SOUTHEAST_POSITIVE_PREVIOUS_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s cJ sJ uJ vJ aJ. %s /\\ %s /\\ %s /\\ %s /\\ &0 < cJ /\\ &0 <= sJ ==> ~%s"
    C1092AE_P C1092MPAPO_HYPS (c1092manh_in 5 "&2" "&87 / &50") C1092MANH_SQJ C1092MANH_FRJ
    (c1092manh_in 5 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MANH_V @ [`cJ:real`; `sJ:real`; `uJ:real`; `vJ:real`; `aJ:real`])
    C1092FPDA_SOUTHEAST_OF_NONPOSITIVE_HALFPOINT) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC (SPECL C1092MANH_V C1092MPAWR_NO_MISSING) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (SPECL C1092MANH_V C1092MANH_NONPOSITIVE_HALFPOINT) THEN ASM_REWRITE_TAC[]]);;

(* Lean: southwest_positive_previous_excluded *)
let C1092MANH_SOUTHWEST_POSITIVE_PREVIOUS_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s cF sF uF vF aF. %s /\\ %s /\\ &0 < cF /\\ &0 <= sF ==> ~%s"
    C1092AE_P C1092MANH_FHYPS (c1092manh_in 4 "&87 / &50" "&2") (c1092manh_in 4 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MANH_ROT3_TAC THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MANH_JROT3) C1092MANH_SOUTHEAST_POSITIVE_PREVIOUS_EXCLUDED) THEN
  c1092mpapo_pull_tac (c1092mpapo_d4 "") `(true,false,true)` [5] THEN ASM_REWRITE_TAC[]);;
