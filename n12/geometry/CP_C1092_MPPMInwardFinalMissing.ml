(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalMissing.lean              *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  Predecessor comparison and  *)
(* final successor join of OPPOSED-MISSING-INWARD sections 2--6.  Squares   *)
(* C W E B R are cC sC uC vC aC, cW .., cE .., cB .., cR ...                 *)
(* MissingProfile: c1092miff_missing_profile; MissingPredecessor:            *)
(* c1092ifm_missingPred; missing_near_center / missing_floor: C1092MIFF_*;   *)
(* predecessor_angle: C1092MIFS_PREDECESSOR_ANGLE; f / g: c1092mifs_f / _g;  *)
(* MMMPUpperThirdScalars.relative_bounds: C1092UTS_RELATIVE_BOUNDS;          *)
(* upward_axes: C1092MIFP_UPWARD_AXES; missing_predecessor_margin:           *)
(* C1092MIFM_MISSING_PREDECESSOR_MARGIN; missing_final_margins:              *)
(* C1092MIFMG_MISSING_FINAL_MARGINS; NegativeSuccessor: c1092ifsu_negsucc.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalMissingScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCentered.ml";;
needs "n12/geometry/CP_C1092_MMMP_UpperThirdScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalFloor.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalPredecessor.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalMargins.ml";;

let C1092IFM_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;

let C1092IFM_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092IFM_LIN; ALL_TAC];;

(* a point fact from an assumption about the same point written differently *)
let C1092IFM_TRANSFER_TAC =
  FIRST_ASSUM ACCEPT_TAC ORELSE
  FIRST_ASSUM(fun th ->
    let t = concl th in let t = if is_neg t then rand t else t in
    if can (term_match [] `linside c s u v a x y`) t
    then MP_TAC th THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC else NO_TAC);;

(* Lean: MissingPredecessor (structure) *)
let c1092ifm_missingPred = new_definition
 `c1092ifm_missingPred (cC:real) (sC:real) (uC:real) (vC:real) (aC:real)
                       (cW:real) (sW:real) (uW:real) (vW:real) (aW:real) <=>
    aC = aW /\ c977cc_normal cW (--sW) /\
    linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
    --cW + sW <= uW /\ (&2 / &5) * cW + sW <= vW /\ vW + aW <= cW /\
    ldisj cC sC uC vC aC cW sW uW vW aW`;;

let C1092IFM_SB_TAC sq (x, y) (nx, ny) =
  MP_TAC(SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN REWRITE_TAC[REAL_POW_2] THEN C1092IFM_LIN;
    STRIP_TAC];;

(* Lean: missing_small *)
let C1092IFM_MISSING_SMALL = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092miff_missing_profile cC sC uC vC aC /\
     c1092ifm_missingPred cC sC uC vC aC cW sW uW vW aW /\
     cC - &1 - sC * (&1 - cC - (&13 / &50) * sC) < cC * (vC + aC)
     ==> C1092WPS_half cC (--sC) < &1 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C1092MIFF_MISSING_NEAR_CENTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[c1092miff_missing_profile] o
    check (can (term_match [] `c1092miff_missing_profile a b c d e`) o concl)) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifm_missingPred] o
    check (can (term_match [] `c1092ifm_missingPred a b c d e f g h i j`) o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  C1092PRS_NORMAL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside] o
    check (fun th -> concl th = `linside cW sW uW vW aC (--(&7 / &20)) (&7 / &20)`)) THEN
  MP_TAC(SPECL [`cW:real`; `--sW`] C1092MIFS_PREDECESSOR_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092UTS_RELATIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
                linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\
                linside cC sC uC vC aC (--(&1 / &25)) (--(&1 / &25))`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN C1092IFM_TRANSFER_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] C1092MIFP_UPWARD_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; ALL_TAC] THEN
  let C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
  and W = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [C1092IFM_SB_TAC C (`--(&1)`, `--(&2 / &5)`) (`--cC`, `--sC`) THEN
    C1092IFM_SB_TAC W (`--(&7 / &20)`, `&7 / &20`) (`--cC`, `--sC`) THEN
    MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092IFM_LIN;
    ALL_TAC;
    C1092IFM_SB_TAC C (`--(&1)`, `--(&2 / &5)`) (`--cW`, `--sW`) THEN
    MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092IFM_LIN;
    C1092IFM_SB_TAC C (`--(&1 / &25)`, `--(&1 / &25)`) (`--sW`, `cW:real`) THEN
    MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092IFM_LIN] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ASM_CASES_TAC `sC * cW - cC * sW <= &0` THENL
   [MP_TAC(SPECL (W @ [`--sC`; `cC:real`; `--(sC * cW - cC * sW)`; `cC * cW + sC * sW`])
      C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; DISCH_TAC] THEN
    C1092IFM_PROD `&0 <= --(sC * cW - cC * sW) * --uW` THEN
    C1092IFM_PROD `&0 <= (cC * cW + sC * sW) * (--(&2 / &17) - vW)` THEN
    C1092IFM_LIN;
    MP_TAC(SPECL (W @ [`--sC`; `cC:real`; `--(sC * cW - cC * sW)`; `cC * cW + sC * sW`])
      C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; DISCH_TAC] THEN
    C1092IFM_PROD `&0 <= (sC * cW - cC * sW) * (uW + cW - sW)` THEN
    C1092IFM_PROD `&0 <= (cC * cW + sC * sW) * (cW - aC - vW)` THEN
    C1092IFM_PROD `&0 < (aC - &1) * ((sC * cW - cC * sW) + (cC * cW + sC * sW))` THEN
    SUBGOAL_THEN `(sC * cW - cC * sW) * (cW - sW - &1) + (cC * cW + sC * sW) * (cW - &1) =
                  cC * c1092mifs_f cW (--sW) + sC * c1092mifs_g cW (--sW)` ASSUME_TAC THENL
     [REWRITE_TAC[c1092mifs_f; c1092mifs_g] THEN
      UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `vC + aC < cC * c1092mifs_f cW (--sW) + sC * c1092mifs_g cW (--sW)`
      ASSUME_TAC THENL [C1092IFM_LIN; ALL_TAC] THEN
    C1092IFM_PROD `&0 < cC * ((cC * c1092mifs_f cW (--sW) + sC * c1092mifs_g cW (--sW)) -
                             (vC + aC))` THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cW:real`; `--sW`] C1092MIFM_MISSING_PREDECESSOR_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; DISCH_TAC] THEN
    C1092IFM_LIN]);;

(* Lean: missing_impossible *)
let C1092IFM_MISSING_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cE sE uE vE aE cB sB uB vB aB cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092miff_missing_profile cC sC uC vC aC /\
     c1092ifm_missingPred cC sC uC vC aC cW sW uW vW aW /\
     aC = aE /\ c1092ifsu_negsucc cE sE uE vE aE /\
     (forall x. --(&14) / &25 <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     (forall y. --(&36 / &85) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
     ldisj cC sC uC vC aC cB sB uB vB aB /\
     ldisj cC sC uC vC aC cE sE uE vE aE /\
     ldisj cE sE uE vE aE cR sR uR vR aR /\
     ldisj cE sE uE vE aE cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092MIFF_MISSING_FLOOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C1092IFM_MISSING_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `~linside cE sE uE vE aE (&1) (--(&36 / &85)) /\
                ~linside cE sE uE vE aE (&0) (--(&1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `ldisj cE sE uE vE aE cR sR uR vR aR` THEN
      REWRITE_TAC[ldisj; NOT_FORALL_THM] THEN
      MAP_EVERY EXISTS_TAC [`&1`; `--(&36 / &85)`] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      UNDISCH_TAC `ldisj cE sE uE vE aE cB sB uB vB aB` THEN
      REWRITE_TAC[ldisj; NOT_FORALL_THM] THEN
      MAP_EVERY EXISTS_TAC [`&0`; `--(&1)`] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> MP_TAC(SPEC `&0` th) THEN
        CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN NO_TAC)];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[c1092miff_missing_profile] o
    check (can (term_match [] `c1092miff_missing_profile a b c d e`) o concl)) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (can (term_match [] `c1092ifsu_negsucc a b c d e`) o concl)) THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
                linside cC sC uC vC aC (&0) (--(&13 / &50))`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN C1092IFM_TRANSFER_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    C1092IFSU_SUCCESSOR_FAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    C1092IFSU_SUCCESSOR_BOTTOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; STRIP_TAC] THEN
  MP_TAC(REWRITE_RULE[C1092IFC_ENDPOINT2] (SPECL [`&4165 / &4813`; `&2412 / &4813`; `cE:real`; `--sE`]
    C1092MIFE_HALF_CROSS)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092MIFMG_MISSING_FINAL_MARGINS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092MIFS_RELATIVE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFM_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `&13 / &50`; `&0`] C1092IFSU_SUCCESSOR_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN C1092IFM_LIN);;
