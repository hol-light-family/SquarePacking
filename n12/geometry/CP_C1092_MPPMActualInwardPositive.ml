(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardPositive.lean            *)
(* (N12Compact.C1092MPPMActualInward).  Genuine original point producers for *)
(* CENTERED-POSITIVE-INWARD.  (Lean header: "Source only".)  Conventions of  *)
(* CP_C1092_MPPMActualInwardSuccessor.ml / MPPMActualInwardFar.ml.           *)
(* outer_nonnegative_impossible C1092IFOW_OUTER_NONNEGATIVE_IMPOSSIBLE;      *)
(* MPPMCenteredPositive.Input c1092mcpd_input, bounds C1092CPS_BOUNDS,       *)
(* height C1092CPH_HEIGHT.  Normal C.c C.s is c977cc_normal cC sC.           *)
(* Tag C1092MPAIP_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardFar.ml";;
needs "n12/geometry/CP_C1092_MPPMCenteredPositiveSuccessor.ml";;
needs "n12/geometry/CP_C1092_MPPMCenteredPositiveHeight.ml";;

let C1092MPAIP_BASE = Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s"
  C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4;;
let C1092MPAIP_CENTER = c1092mpais_in 4 "&2" "&2";;

(* Lean: nonnegative_outer_missing *)
let C1092MPAIP_NONNEGATIVE_OUTER_MISSING = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ c977cc_normal cC sC /\\ %s ==> ~%s"
    C1092AE_P C1092MPAIP_BASE (c1092mpais_frame 4 "C") (c1092mpais_unit "C") (c1092mpais_in 4 "&1" "&8 / &5")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAI_BOTTOM_BAR THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTRAL_ANCHORS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`4`; `9`] @ C1092MPAIS_C @ C1092MPAIM_CH9) C1092MPAI_FRAME_APART) THEN
  ASM_REWRITE_TAC[SPECL (C1092MPPE_V @ [`9`]) C1092MPAI_CHART_FRAME; ARITH] THEN DISCH_TAC THEN
  C1092MPAIM_NOT_ORDINARY_TAC THEN
  C1092MPAI_INWARD_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&13 / &50)` `&0`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&1)` `--(&2 / &5)`) [] THEN
  c1092mpais_fact "C" (mk_neg (c1092mpais_cin "C" `--(&1)` `--(&13 / &50)`)) [] THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIM_CH9) C1092IFOW_OUTER_NONNEGATIVE_IMPOSSIBLE) THEN
  ASM_SIMP_TAC C1092MPAIF_SIMP THEN c1092mpaif_close_tac);;

let C1092MPAIP_DATA_HYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cC sC /\\ %s"
  C1092MPAIP_BASE C1092MPAIP_CENTER (c1092mpais_frame 4 "C") (c1092mpais_frame 5 "E") (c1092mpais_unit "C");;

(* Lean: centered_positive_data *)
let C1092MPAIP_CENTERED_POSITIVE_DATA = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC cE sE uE vE aE. %s ==> c1092mcpd_input cC sC uC vC aC cE sE uE vE aE"
    C1092AE_P C1092MPAIP_DATA_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092MIN_SOUTHWEST_CROSSPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MIN_SOUTHEAST_PAIR THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAI_SUCCESSOR_HALFPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAI_RIGHT_ORIGIN THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAI_RIGHT_BAR THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTRAL_ANCHORS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIP_NONNEGATIVE_OUTER_MISSING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAI_MISSING_OUTER_SHARP THEN DISCH_TAC THEN
  c1092mpais_apart_tac 4 "C" 5 "E" THEN
  SUBGOAL_THEN (parse_term (c1092mpais_in 10 "&3" "&161 / &100")) ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `--(&39 / &100)` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `EL 10 c1092wc_code`)) (concl th))) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  C1092MPAI_INWARD_TAC THEN
  let lit i x y = c1092moc_excl 5 i (CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term (c1092mpais_in i x y)))) in
  c1092mpais_fact "C" (c1092mpais_cin "C" `&0` `&0`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&1 / &2)` `&0`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `&0` `--(&13 / &50)`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&1 / &100)` `--(&27 / &50)`) [] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&7 / &20` `--(&7 / &20)`) [c1092moc_seed 5 (`&47 / &20`, `&33 / &20`)] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&13 / &50` `--(&1)`) [] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&2 / &5` `--(&1)`) [] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&1 / &2` `--(&1)`) [] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `--(&39 / &100)`)) [lit 10 "&3" "&161 / &100"] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&0` `--(&543 / &500)`))
    [c1092moc_excl 5 9 (c1092moc_seed 9 (`&2`, `&457 / &500`))] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `--(&1)`))
    [c1092moc_excl 5 1 (c1092moc_seed 1 (`&3`, `&1`))] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `&0`)) [lit 10 "&3" "&2"] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `--(&2 / &5)`))
    [c1092moc_excl 5 10 (ASSUME (c1092mpais_lit 10 `&3` `&8 / &5`))] THEN
  REWRITE_TAC[c1092mcpd_input] THEN ASM_REWRITE_TAC[]);;

let C1092MPAIP_BOUNDS_HYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ c977cc_normal cC sC /\\ %s"
  C1092MPAIP_BASE C1092MPAIP_CENTER (c1092mpais_frame 4 "C") (c1092mpais_unit "C");;

(* Lean: centered_positive_bounds *)
let C1092MPAIP_CENTERED_POSITIVE_BOUNDS = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> &99 / &100 < cC /\\ sC < &7 / &50 /\\ &93 / &500 + (&33 / &50) * sC < vC + aC /\\ uC + aC <= (&7 / &50) * cC - sC / &2"
    C1092AE_P C1092MPAIP_BOUNDS_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 5 "E" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIP_CENTERED_POSITIVE_DATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_C @ C1092MPAIS_E) C1092CPS_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN c1092mpaif_close_tac);;

(* Lean: centered_nonnegative_impossible *)
let C1092MPAIP_CENTERED_NONNEGATIVE_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> F" C1092AE_P C1092MPAIP_BOUNDS_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIP_CENTERED_POSITIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mpaif_canon_tac 7 "W" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_W) C1092MPAI_PREDECESSOR_POINTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpais_apart_tac 4 "C" 7 "W" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTRAL_ANCHORS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (c1092mpais_cin "C" `&0` `&0`) ASSUME_TAC THENL
   [C1092MPAIS_FRAME_CONV_TAC "C" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPAIS_C @ C1092MPAIS_W) C1092CPH_HEIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN c1092mpaif_close_tac; DISCH_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`sC < &7 / &50`; `&93 / &500 + (&33 / &50) * sC < vC + aC`;
                         `vC + aC < &17 / &125 + sC`] THEN REAL_ARITH_TAC);;

(* Lean: centered_sign *)
let C1092MPAIP_CENTERED_SIGN = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ %s /\\ %s /\\ abs sC <= cC ==> sC < &0"
    C1092AE_P C1092MPAIP_BASE C1092MPAIP_CENTER (c1092mpais_frame 4 "C") (c1092mpais_unit "C")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIP_CENTERED_NONNEGATIVE_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  MAP_EVERY UNDISCH_TAC [`abs sC <= cC`; `&0 <= sC`] THEN REAL_ARITH_TAC);;
