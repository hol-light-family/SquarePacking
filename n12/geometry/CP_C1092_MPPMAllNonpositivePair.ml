(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositivePair.lean              *)
(* (N12Compact.C1092MPPMAllNonpositive), ALL-NEGATIVE-MIXED-FORWARD-ENDING  *)
(* section 3.  Squares C = cC sC uC vC aC and E = cE sE uE vE aE with their  *)
(* OpenSquare invariants as hypotheses.  Core / faces: c1092anc_core /       *)
(* C1092ANC_FACES; ClearedSuccessor c1092manp_clearedSuccessor;              *)
(* TripleScalars G / k / delta / source_* / target_*: c1092ants_* /          *)
(* C1092ANTS_*; OrdinaryNegativeHalfpoint Frame / axes: c1092onh_frame /     *)
(* C1092ONHF_AXES; lower / upper ABT_lower / ABT_upper; lower_pn / lower_nn /*)
(* formulas C1092WS_*.  The Lean lets are written out: with c = cC,          *)
(* s = --sC, d = cE, t = --sE, k = cC * cE + sC * sE and                    *)
(* z = --cC * sE + sC * cE.  Tag C1092MANPP_.                                *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositiveProfiles.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveTripleScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryNegativeHalfpointFaces.ml";;

let C1092MANPP_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;
let C1092MANPP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MANPP_LP_TAC; ALL_TAC];;
let C1092MANPP_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092MANPP_LP_TAC; ALL_TAC];;

(* Lean: pair_impossible *)
let C1092MANPP_PAIR_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092anc_core cC sC uC vC aC /\ &873 / &1000 < cC /\
     c1092manp_clearedSuccessor cE sE uE vE aE /\ aC = aE /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o check (c1092mpapo_head `c1092anc_core`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092manp_clearedSuccessor] o
    check (c1092mpapo_head `c1092manp_clearedSuccessor`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`;
                `uE:real`; `vE:real`; `aE:real`] C1092ONHF_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092onh_frame] THEN
    MAP_EVERY (fun (c, s) -> c1092mabo_normal_tac c s) [`cC:real`, `--sC`; `cE:real`, `--sE`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MAP_EVERY (fun (c, s) -> c1092mabo_normal_tac c s) [`cC:real`, `--sC`; `cE:real`, `--sE`] THEN
  (* the forward point gives (13/50) * sC < vC + aC *)
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[linside] o check (fun th ->
    concl th = `linside cC sC uC vC aC (--(&13 / &50)) (&0)`)) THEN STRIP_TAC THEN
  C1092MANPP_FACT `&0 < cC /\ &0 < cE /\ &0 < --sC /\ &0 < --sE` THEN
  C1092MANPP_PROD `&0 < cC * cE` THEN C1092MANPP_PROD `&0 < --sC * --sE` THEN
  C1092MANPP_FACT `&0 < cC * cE + sC * sE` THEN
  C1092MANPP_PROD `&0 < cE * (cC * cE + sC * sE)` THEN
  SUBGOAL_THEN `cE * c1092ants_G cE (--sE) = (&1 - cE) * (&1 - --sE)` ASSUME_TAC THENL
   [REWRITE_TAC[c1092ants_G] THEN
    SUBGOAL_THEN `~(cE = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* vertex and its weighted consequences *)
  C1092MANPP_PROD `&0 < (cC * cE + sC * sE) * (&1 - (cE * (uE + aC) - sE * (vE + aC)))` THEN
  C1092MANPP_PROD `&0 <= --sC * ((vE + aC) - (aC - cE))` THEN
  C1092MANPP_PROD `&0 <= --sE * ((vE + aC) - (aC - cE))` THEN
  ASM_CASES_TAC `c1092ants_delta cC (--sC) cE (--sE) <= &0` THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[c1092ants_delta; REAL_NOT_LE] o
    check (fun th -> can (find_term ((=) `c1092ants_delta`)) (concl th))) THENL
   [(* before: z <= 0 *)
    C1092MANPP_FACT `--cC * sE + sC * cE <= &0` THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [(* current *)
      MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
        `cC * cE + sC * sE`; `--cC * sE + sC * cE`] C1092WS_LOWER_PN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANPP_LP_TAC; DISCH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `ABT_lower`)) (concl th) && not (is_eq (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092ANTS_SOURCE_BEFORE) THEN
      ASM_REWRITE_TAC[c1092ants_k] THEN DISCH_TAC THEN
      C1092MANPP_PROD `&0 <= cE * (uC - --cC)` THEN
      C1092MANPP_PROD `&0 <= cE * (((cC * cE + sC * sE) * uE + (--cC * sE + sC * cE) * (vE + aC)) - (uC + aC))` THEN
      SUBGOAL_THEN `cE * ((cC * cE + sC * sE) * uE + (--cC * sE + sC * cE) * (vE + aC)) =
                    (cC * cE + sC * sE) * (cE * (uE + aC) - sE * (vE + aC)) - --sC * (vE + aC) -
                    aC * cE * (cC * cE + sC * sE)` ASSUME_TAC THENL
       [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      C1092MANPP_PROD `&0 < (aC - &1) * (cE + --sC + cE * (cC * cE + sC * sE))` THEN
      C1092MANPP_LP_TAC;
      (* recipient *)
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`] C1092WS_FORMULAS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
      SUBGOAL_THEN `max (cE * cC + sE * sC) (&0) = cE * cC + sE * sC /\
                    max (--cE * sC + sE * cC) (&0) = --cE * sC + sE * cC` ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> max x (&0) = x`) THEN C1092MANPP_LP_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `ABT_upper`)) (concl th) && not (is_eq (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092ANTS_TARGET_BEFORE) THEN
      ASM_REWRITE_TAC[c1092ants_k; c1092ants_delta] THEN DISCH_TAC THEN
      C1092MANPP_PROD `&0 <= (cC * cE + sC * sE) * (uC - --cC)` THEN
      C1092MANPP_PROD `&0 <= --(--cC * sE + sC * cE) * ((vC + aC) - (&13 / &50) * sC)` THEN
      C1092MANPP_PROD `&0 < cE * ((cC * cE + --sC * --sE) * (&1 - cC) +
          &13 / &50 * (cC * --sE - --sC * cE) * --sC - c1092ants_G cE (--sE))` THEN
      C1092MANPP_PROD `&0 < (aC - &1) * (cE * (&1 + (cC * cE + sC * sE)) + --sE)` THEN
      C1092MANPP_PROD `&0 <= cE * (uE - ((cC * cE + sC * sE) * (aC - cC) +
          (&13 / &50) * (--cC * sE + sC * cE) * --sC))` THEN
      C1092MANPP_LP_TAC];
    (* after: z >= 0 *)
    C1092MANPP_FACT `&0 <= --cC * sE + sC * cE` THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [(* current *)
      MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
        `cC * cE + sC * sE`; `--cC * sE + sC * cE`] C1092WS_LOWER_NN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANPP_LP_TAC; DISCH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `ABT_lower`)) (concl th) && not (is_eq (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(REWRITE_RULE[c1092ants_k; c1092ants_delta]
        (SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092ANTS_SOURCE_AFTER)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANPP_LP_TAC; DISCH_TAC] THEN
      C1092MANPP_PROD `&0 <= cE * (uC - --cC)` THEN
      C1092MANPP_PROD `&0 <= cE * (((cC * cE + sC * sE) * uE + (--cC * sE + sC * cE) * vE) - (uC + aC))` THEN
      SUBGOAL_THEN `cE * ((cC * cE + sC * sE) * uE + (--cC * sE + sC * cE) * vE) =
                    (cC * cE + sC * sE) * (cE * (uE + aC) - sE * (vE + aC)) - --sC * (vE + aC) -
                    aC * cE * ((cC * cE + sC * sE) + (--cC * sE + sC * cE))` ASSUME_TAC THENL
       [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      C1092MANPP_PROD `&0 <= cE * (--cC * sE + sC * cE)` THEN
      C1092MANPP_PROD `&0 < (aC - &1) * (cE + --sC + cE * ((cC * cE + sC * sE) + (--cC * sE + sC * cE)))` THEN
      C1092MANPP_LP_TAC;
      (* recipient *)
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`] C1092WS_FORMULAS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
      SUBGOAL_THEN `max (cE * cC + sE * sC) (&0) = cE * cC + sE * sC /\
                    max (--cE * sC + sE * cC) (&0) = &0` ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> max x (&0) = x`);
          MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> max x (&0) = &0`)] THEN C1092MANPP_LP_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `ABT_upper`)) (concl th) && not (is_eq (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(REWRITE_RULE[c1092ants_k; c1092ants_delta]
        (SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092ANTS_TARGET_AFTER)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANPP_LP_TAC; DISCH_TAC] THEN
      C1092MANPP_PROD `&0 <= (cC * cE + sC * sE) * (uC - --cC)` THEN
      C1092MANPP_PROD `&0 <= (--cC * sE + sC * cE) * ((&7 / &20) * (cC + sC) - (vC + aC))` THEN
      C1092MANPP_PROD `&0 < cE * ((cC * cE + --sC * --sE) * (&1 - cC) +
          (cC * --sE - --sC * cE) * (&1 - &7 / &20 * (cC - --sC)) - c1092ants_G cE (--sE))` THEN
      C1092MANPP_PROD `&0 <= cE * (--cC * sE + sC * cE)` THEN
      C1092MANPP_PROD `&0 < (aC - &1) * (cE * (&1 + (cC * cE + sC * sE) + (--cC * sE + sC * cE)) + --sE)` THEN
      C1092MANPP_PROD `&0 <= cE * (uE - ((cC * cE + sC * sE) * (aC - cC) +
          (--cC * sE + sC * cE) * (aC - (&7 / &20) * (cC + sC))))` THEN
      C1092MANPP_LP_TAC]]);;
