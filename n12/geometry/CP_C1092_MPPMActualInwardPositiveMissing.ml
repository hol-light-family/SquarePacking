(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardPositiveMissing.lean     *)
(* (N12Compact.C1092MPPMActualInward).  Literal actual entrance for positive *)
(* missing-center inward C.  (Lean header: "Source only, uncompiled".)       *)
(* Conventions of CP_C1092_MPPMActualInwardPositive.ml / MPPMActualInward-   *)
(* Predecessor.ml: owners p i at mask EL i c1092wc_code (side l); Frame p i  *)
(* C is c1092mpai_frame c1 c2 a b l i cC sC uC vC aC (unit normal / positive *)
(* side of C, E explicit); chart p i the tuple c1092mpai_chart i (insides    *)
(* through C1092PSA_INSIDE_TRANSLATED).  MPPMInwardPositive.PairInput        *)
(* c1092ipsf_pair, Input c1092ipp_input, recipient data c1092minf_data;      *)
(* no_missing / wall_pairs C1092MPAWR_*; southeast_pair /                    *)
(* southwest_crosspoint C1092MIN_*; central_anchors C1092MPAIS_CENTRAL_      *)
(* ANCHORS; nonnegative_outer_missing C1092MPAIP_NONNEGATIVE_OUTER_MISSING;  *)
(* missing_outer_sharp / successor_halfpoint / right_origin C1092MPAI_*;     *)
(* marker_owned / corner_points / owners_disjoint via c1092moc_seed /        *)
(* c1092moc_excl.  g.pullPacking p (g = (F,T,T)) via C1092MPAID_SETUP_TAC /  *)
(* c1092mpaid_tr_tac.  inside_segment C1092WC_INSIDE_SEGMENT.                *)
(* Tag C1092MPAIPM_.                                                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardPositive.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveSuccessor.ml";;
needs "n12/geometry/CP_C1092_MPPMActualInwardPredecessor.ml";;

let C1092MPAIPM_INPUT_HYPS = Printf.sprintf "%s /\\ ~%s /\\ %s /\\ %s /\\ c977cc_normal cC sC /\\ %s /\\ %s"
  C1092MPAIP_BASE (c1092mpais_in 4 "&2" "&2") (c1092mpais_frame 4 "C") (c1092mpais_frame 5 "E")
  (c1092mpais_unit "C") (c1092mpais_unit "E");;

(* Lean: positive_missing_input *)
let C1092MPAIPM_POSITIVE_MISSING_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC cE sE uE vE aE. %s ==> c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE"
    C1092AE_P C1092MPAIPM_INPUT_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092MIN_SOUTHWEST_CROSSPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MIN_SOUTHEAST_PAIR THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAI_SUCCESSOR_HALFPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTRAL_ANCHORS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIP_NONNEGATIVE_OUTER_MISSING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAI_MISSING_OUTER_SHARP THEN DISCH_TAC THEN
  c1092mpais_apart_tac 4 "C" 5 "E" THEN
  C1092MPAI_INWARD_TAC THEN
  let lit i x y = CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term (c1092mpais_in i x y))) in
  c1092mpais_fact "C" (c1092mpais_cin "C" `&0` `--(&13 / &50)`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&13 / &50)` `&0`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&1 / &2)` `&0`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&1 / &100)` `--(&27 / &50)`) [] THEN
  c1092mpais_fact "C" (mk_neg (c1092mpais_cin "C" `&0` `&0`)) [] THEN
  c1092mpais_fact "C" (mk_neg (c1092mpais_cin "C" `--(&1)` `--(&2 / &5)`)) [] THEN
  c1092mpais_fact "C" (mk_neg (c1092mpais_cin "C" `--(&2 / &5)` `--(&1)`))
    [c1092moc_excl 4 9 (lit 9 "&8 / &5" "&1")] THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < aE` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `aC:real = aE` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&7 / &20` `--(&7 / &20)`) [c1092moc_seed 5 (`&47 / &20`, `&33 / &20`)] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&13 / &50` `--(&1)`) [] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&2 / &5` `--(&1)`) [] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&1 / &2` `--(&1)`) [] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&0` `--(&13 / &50)`))
    [c1092moc_excl 5 4 (lit 4 "&2" "&87 / &50")] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `--(&2 / &5)`))
    [c1092moc_excl 5 10 (lit 10 "&3" "&8 / &5")] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&0` `--(&543 / &500)`))
    [c1092moc_excl 5 9 (c1092moc_seed 9 (`&2`, `&457 / &500`))] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `--(&1)`))
    [c1092moc_excl 5 1 (c1092moc_seed 1 (`&3`, `&1`))] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `--(&543 / &500)`))
    [c1092moc_excl 5 1 (c1092moc_seed 1 (`&3`, `&457 / &500`))] THEN
  REWRITE_TAC[c1092ipsf_pair; c1092ipp_input; c1092minf_data] THEN ASM_REWRITE_TAC[]);;

(* Lean: opposite_inward_left_origin *)
let C1092MPAIPM_OPPOSITE_INWARD_LEFT_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s /\\ %s ==> %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX (c1092mpais_in 6 "&2" "&113 / &50") (c1092mpais_in 6 "&113 / &50" "&2")
    (c1092mpais_in 8 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MPAID_SETUP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "c1092mcc_inward %s" (c1092ae_own "d1 d2 e1 e2 l" 4)))
    ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcc_inward] THEN c1092mpaid_tr_tac 4 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL C1092MPAID_D5 C1092MPAI_RIGHT_ORIGIN) THEN ASM_REWRITE_TAC[] THEN
  c1092mpaid_tr_tac 10 THEN REWRITE_TAC[]);;

(* Lean: left_seed_points *)
let C1092MPAIPM_LEFT_SEED_POINTS = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s /\\ %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX
    (string_of_term (c1092mpai_chin "8" `--(&543 / &500)` `&0`))
    (string_of_term (c1092mpai_chin "8" `--(&1)` `&13 / &50`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
  REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092MOC_CODE_CONV THEN REWRITE_TAC[c1092moc_seed 8 (`&457 / &500`, `&2`)]);;

(* Lean: left_seed_segment *)
let C1092MPAIPM_LEFT_SEED_SEGMENT = prove
 (parse_term (Printf.sprintf "!%s t. %s /\\ %s /\\ &0 <= t /\\ t <= &1 ==> %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX
    (string_of_term (c1092mpai_chin "8" `--(&543 / &500) + (&43 / &500) * t` `(&13 / &50) * t`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPAIPM_LEFT_SEED_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (c1092mpai_chart "8" @ [`--(&543 / &500)`; `&0`; `--(&1)`; `&13 / &50`; `t:real`])
    C1092WC_INSIDE_SEGMENT) THEN
  ASM_REWRITE_TAC[REAL_ARITH `(&1 - t) * --(&543 / &500) + t * --(&1) = --(&543 / &500) + (&43 / &500) * t`;
                  REAL_ARITH `(&1 - t) * &0 + t * (&13 / &50) = (&13 / &50) * t`]);;
