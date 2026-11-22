(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardMissing.lean             *)
(* (N12Compact.C1092MPPMActualInward).  The two genuine missing-center       *)
(* alternatives in original MPPM.  (Lean header: "Source only, uncompiled".) *)
(* Conventions of CP_C1092_MPPMActualInwardPoints.ml: owners p i at mask     *)
(* EL i c1092wc_code (side l); WallContext p mppm C1092MPPE_CTX; Inward /    *)
(* Ordinary c1092mcc_inward / c1092mcc_ordinary; Frame p i C is              *)
(* c1092mpai_frame c1 c2 a b l i cC sC uC vC aC (C's unit normal / positive  *)
(* side as explicit hypotheses where the conclusion needs them); chart p i   *)
(* the tuple c1092mpai_chart i; Frame.apart C1092MPAI_FRAME_APART, chart_    *)
(* frame C1092MPAI_CHART_FRAME, bottom_bar C1092MPAI_BOTTOM_BAR,             *)
(* missing_outer_sharp C1092MPAI_MISSING_OUTER_SHARP.  OuterOwnedInput      *)
(* c1092ifow_input, outer_owned_profile / _halfpoint C1092IFOW_*;            *)
(* BottomAngle.Input c1092ifbd_input, BottomAngle.angle C1092IFBA_ANGLE;     *)
(* MissingProfile c1092miff_missing_profile; Normal c977cc_normal; half      *)
(* C1092WPS_half.  marker_owned = oo_seed (c1092moc_seed); (hb 1).1 with     *)
(* center_translate_x = C1092MOC_BOTTOM_CUT + lcx algebra.  Used neighbours: *)
(* C1092MIN_SOUTHWEST_CROSSPOINT / BOTTOM_FAR, C1092MPAWR_NO_MISSING /       *)
(* WALL_PAIRS, C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT.  Tag C1092MPAIM_.        *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardPoints.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalOuterOwned.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomAngle.ml";;

let C1092MPAIM_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092MPAIM_CH9 = c1092mpai_chart "9";;
let c1092mpaim_tuple ts = String.concat " " (map (fun t -> "(" ^ string_of_term t ^ ")") ts);;
let C1092MPAIM_CH9S = c1092mpaim_tuple C1092MPAIM_CH9;;
let C1092MPAIM_FRAME4 = "c1092mpai_frame c1 c2 a b l 4 cC sC uC vC aC";;
let C1092MPAIM_UNIT = "cC * cC + sC * sC = &1 /\\ &0 < aC";;
let c1092mpaim_in = c1092mppe_in;;

(* Frame.apart of the frame of owner i (in the assumptions) and chart j *)
let c1092mpaim_apart_tac i j =
  MP_TAC(SPECL (C1092MPPE_V @ [mk_small_numeral i; mk_small_numeral j] @ C1092MPAIM_C @
                c1092mpai_chart (string_of_int j)) C1092MPAI_FRAME_APART) THEN
  ASM_REWRITE_TAC[SPECL (C1092MPPE_V @ [mk_small_numeral j]) C1092MPAI_CHART_FRAME; ARITH] THEN
  DISCH_TAC;;

let c1092mpaim_is_frame th =
  let t = concl th in is_comb t && fst (strip_comb t) = `c1092mpai_frame`;;

(* open the frame of C: aC := l, the equivalence as an assumption *)
let C1092MPAIM_FRAME_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpai_frame] o check c1092mpaim_is_frame) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`));;

let C1092MPAIM_NOT_ORDINARY_TAC =
  SUBGOAL_THEN (mk_neg (parse_term (c1092mpaim_in 4 "&1" "&87 / &50"))) ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term ((=) `c1092mcc_ordinary`)) (concl th))) THEN
    REWRITE_TAC[c1092mcc_ordinary] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let C1092MPAIM_OWNED_HYPS = Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ ~%s /\\ %s"
  C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4
  (c1092mpaim_in 4 "&1" "&8 / &5") (c1092mpaim_in 4 "&2" "&2") C1092MPAIM_FRAME4;;

(* Lean: outer_owned_input *)
let C1092MPAIM_OUTER_OWNED_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> c1092ifow_input cC sC uC vC aC %s"
    C1092AE_P C1092MPAIM_OWNED_HYPS C1092MPAIM_CH9S),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MPAIM_NOT_ORDINARY_TAC THEN
  c1092mpai_use C1092MPAI_BOTTOM_BAR THEN DISCH_TAC THEN
  C1092MPAI_INWARD_TAC THEN
  c1092mpaim_apart_tac 4 9 THEN
  C1092MPAIM_FRAME_TAC THEN
  REWRITE_TAC[c1092ifow_input] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092MOC_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN
  ASM_REWRITE_TAC[c1092moc_side (); c1092moc_seed 4 (`&33 / &20`, `&33 / &20`); IMP_CONJ] THEN
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV))]);;

(* Lean: outer_owned *)
let C1092MPAIM_OUTER_OWNED = prove
 (parse_term (Printf.sprintf
   "!%s cC sC uC vC aC. %s /\\ %s /\\ abs sC <= cC ==> c1092miff_missing_profile cC sC uC vC aC /\\ C1092WPS_half cC (--sC) < &1 - sqrt(&13) / &5 /\\ %s /\\ %s"
    C1092AE_P C1092MPAIM_OWNED_HYPS C1092MPAIM_UNIT
    (c1092mpaim_in 4 "&1" "&3 / &2") (c1092mpaim_in 9 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIM_C) C1092MPAIM_OUTER_OWNED_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPAIM_C @ C1092MPAIM_CH9) C1092IFOW_OUTER_OWNED_PROFILE) THEN
  ASM_SIMP_TAC[OO_UNIT; OO_SIDE; REAL_ARITH `&1 < l ==> &0 < l`] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPAIM_C @ C1092MPAIM_CH9) C1092IFOW_OUTER_OWNED_HALFPOINT) THEN
  ASM_SIMP_TAC[OO_UNIT; OO_SIDE; REAL_ARITH `&1 < l ==> &0 < l`] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpai_frame] o check c1092mpaim_is_frame) THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `cC:real`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL C1092MPPE_V C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT) THEN ASM_REWRITE_TAC[]);;

let C1092MPAIM_OMITTED_HYPS = Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s /\\ ~%s /\\ ~%s /\\ %s /\\ c977cc_normal cC (--sC)"
  C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4
  (c1092mpaim_in 4 "&1" "&8 / &5") (c1092mpaim_in 4 "&2" "&2") C1092MPAIM_FRAME4;;

(* Lean: outer_omitted_input *)
let C1092MPAIM_OUTER_OMITTED_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> c1092ifbd_input cC sC uC vC aC %s"
    C1092AE_P C1092MPAIM_OMITTED_HYPS C1092MPAIM_CH9S),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092MIN_SOUTHWEST_CROSSPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MIN_BOTTOM_FAR THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAI_MISSING_OUTER_SHARP THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
  c1092mpai_use C1092MOC_BOTTOM_CUT THEN DISCH_TAC THEN
  C1092MPAI_INWARD_TAC THEN
  c1092mpaim_apart_tac 4 9 THEN
  C1092MPAIM_FRAME_TAC THEN
  REWRITE_TAC[c1092ifbd_input] THEN ASM_REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092MOC_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN
  ASM_REWRITE_TAC[c1092moc_side (); c1092moc_seed 4 (`&33 / &20`, `&33 / &20`);
                  c1092moc_seed 9 (`&2`, `&457 / &500`)] THEN
  REPEAT CONJ_TAC THEN FIRST
   [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092moc_box 9))) THEN
    REAL_ARITH_TAC;
    MP_TAC (c1092moc_unit 9) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `lcx`)) (concl th))) THEN
    REWRITE_TAC[lcx] THEN REAL_ARITH_TAC]);;

(* Lean: outer_omitted_angle *)
let C1092MPAIM_OUTER_OMITTED_ANGLE = prove
 (parse_term (Printf.sprintf
   "!%s cC sC uC vC aC. %s /\\ %s ==> &0 < C1092WPS_half cC (--sC) /\\ C1092WPS_half cC (--sC) < &1 - &2 * sqrt(&5) / &5 /\\ C1092WPS_half cC (--sC) < &53 / &500"
    C1092AE_P C1092MPAIM_OMITTED_HYPS C1092MPAIM_UNIT),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIM_C) C1092MPAIM_OUTER_OMITTED_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MPAIM_C @ C1092MPAIM_CH9) C1092IFBA_ANGLE) THEN
  ASM_SIMP_TAC[OO_UNIT; OO_SIDE; REAL_ARITH `&1 < l ==> &0 < l`]);;
