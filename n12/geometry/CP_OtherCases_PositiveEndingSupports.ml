(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/PositiveEndingSupports.lean        *)
(* (N12Compact.Completion.OtherCases.PositiveEndingSupports).  Support       *)
(* comparisons for every surviving face normal of the positive southeast     *)
(* ending.  W = (cW,sW,uW,vW,aW), E = (cE,sE,uE,vE,aE); Lean upper / lower   *)
(* (ThreeSquare / ABTransverse) = ABT_upper / ABT_lower, strict_bounds =     *)
(* ABT_STRICT_BOUNDS, ownU / ownV = ABT_OWNU / ABT_OWNV, WallProfile         *)
(* upper_neg / lower_neg = OCWPVG_*_NEG, SupportBands = OCSB_*,              *)
(* PositiveEndingFaces.Data E = ocpef_data cE sE uE vE aE (with the unit /   *)
(* side_pos hypotheses of E separately), half = C1092WPS_half.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_PositiveEndingWalls.ml";;
needs "n12/geometry/CP_OtherCases_SupportBands.ml";;
needs "n12/geometry/CP_OtherCases_PositiveEndingFaces.ml";;
needs "n12/geometry/CP_OtherCases_InwardSignScalars.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let OCPESU_FACT tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;
let OCPESU_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   RASM_ARITH_TAC; ALL_TAC];;
(* REAL_ARITH from the listed assumptions only *)
let OCPESU_USE tms = MAP_EVERY (MP_TAC o ASSUME) tms THEN REAL_ARITH_TAC;;
(* positive cancellation: &0 < k /\ k * x < k * y ==> x < y *)
let OCPESU_CANCEL = prove
 (`forall k x y. &0 < k /\ k * x < k * y ==> x < y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `x - y`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC);;
let OCPESU_DATA_TAC =
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[ocpef_data] o
    check (fun th -> can (term_match [] `ocpef_data c s u v a`) (concl th)));;

(* Lean: floor_upper (private) *)
let OCPESU_FLOOR_UPPER = prove
 (`forall cE sE uE vE aE. cE * cE + sE * sE = &1 /\ &0 < aE /\ ocpef_data cE sE uE vE aE /\
     --(&1) <= sE * uE + cE * vE ==> --(&12 / &113) < vE + aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCPESU_DATA_TAC THEN
  OCPESU_PROD `&0 <= sE * (cE - (uE + aE))` THEN
  OCPESU_PROD `&0 <= sE * (&1 - cE)` THEN
  OCPESU_PROD `&0 < (aE - &1) * (cE + sE)` THEN
  OCPESU_FACT `&0 < cE * ((vE + aE) + &12 / &113)`
   (OCPESU_USE [`--(&1) <= sE * uE + cE * vE`; `&0 <= sE * (cE - (uE + aE))`;
                `&0 <= sE * (&1 - cE)`; `&0 < (aE - &1) * (cE + sE)`; `&113 / &125 < cE`]) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x + &12 / &113 ==> --(&12 / &113) < x`) THEN
  MATCH_MP_TAC OCPESU_CANCEL THEN EXISTS_TAC `cE:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_RZERO]]);;

(* Lean: own_axis *)
let OCPESU_OWN_AXIS = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     ocpef_data cE sE uE vE aE /\
     linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     ABT_upper cW sW uW vW aW sE (--cE) <= ABT_lower cE sE uE vE aE sE (--cE)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `--(&7 / &20)`; `--(&7 / &20)`; `sE:real`; `--cE`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING;
    STRIP_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`; `cE:real`]
    OCWPVG_LOWER_NEG) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ASSUME `ocpef_data cE sE uE vE aE`) THEN REWRITE_TAC[ocpef_data] THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`] OCISS_PROJECTION_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] OCPESU_FLOOR_UPPER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN RASM_ARITH_TAC]);;

(* Lean: negative_support (private) *)
let OCPESU_NEGATIVE_SUPPORT = prove
 (`forall cW sW cE sE uE vE aE r. cW * cW + sW * sW = &1 /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     sW = --r /\ &0 < cW /\ &0 <= r /\ r <= cW /\ ocpef_data cE sE uE vE aE
     ==> ABT_lower cE sE uE vE aE cW (--r) < &1 - cW /\
         ABT_lower cE sE uE vE aE cW (--r) < &7 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCPESU_DATA_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --r`)) THEN
  OCPESU_FACT `cE pow 2 + sE pow 2 = &1` (ASM_REWRITE_TAC[REAL_POW_2]) THEN
  OCPESU_FACT `cW pow 2 + r pow 2 = &1`
    (UNDISCH_TAC `cW * cW + --r * --r = &1` THEN CONV_TAC REAL_RING) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `r:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  OCPESU_PROD `&0 <= cW * (cE - sE)` THEN
  OCPESU_PROD `&0 <= sE * (cW - r)` THEN
  OCPESU_FACT `&0 <= cE * cW - sE * r`
    (OCPESU_USE [`&0 <= cW * (cE - sE)`; `&0 <= sE * (cW - r)`]) THEN
  OCPESU_PROD `&0 < sE * cW` THEN
  OCPESU_PROD `&0 <= cE * r` THEN
  OCPESU_FACT `&0 < sE * cW + cE * r` (OCPESU_USE [`&0 < sE * cW`; `&0 <= cE * r`]) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `cW:real`; `--r`]
    OCSB_LOWER_PN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MAP_EVERY (MP_TAC o ASSUME) [`&0 <= cE * cW - sE * r`; `&0 < sE * cW + cE * r`] THEN
    REAL_ARITH_TAC; DISCH_TAC] THEN
  OCPESU_FACT `ABT_lower cE sE uE vE aE cW (--r) =
     (cE * cW - sE * r) * uE - (sE * cW + cE * r) * (vE + aE)`
    (ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* face *)
    OCPESU_PROD `&0 <= (cE * cW - sE * r) * (cE - (uE + aE))` THEN
    OCPESU_PROD `&0 <= (sE * cW + cE * r) * (vE + cE + &13 / &50 * sE)` THEN
    OCPESU_PROD `&0 < (aE - &1) * ((cE * cW - sE * r) + (sE * cW + cE * r))` THEN
    OCPESU_FACT `ABT_lower cE sE uE vE aE cW (--r) <
       cW * ((cE - &1) * (cE + sE) + &13 / &50 * sE pow 2) +
       r * ((cE - &1) * (cE - sE) + &13 / &50 * cE * sE)`
     (ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`&0 <= (cE * cW - sE * r) * (cE - (uE + aE))`;
        `&0 <= (sE * cW + cE * r) * (vE + cE + &13 / &50 * sE)`;
        `&0 < (aE - &1) * ((cE * cW - sE * r) + (sE * cW + cE * r))`] THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC) THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `cW:real`; `r:real`] OCPES_BAR_NORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`] OCPES_BAR_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
    OCPESU_PROD `&0 < cW * --((cE - &1) * (cE + sE) + &13 / &50 * sE pow 2)` THEN
    OCPESU_PROD `&0 <= r * (&7 / &100 - ((cE - &1) * (cE - sE) + &13 / &50 * cE * sE))` THEN
    CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`ABT_lower cE sE uE vE aE cW (--r) <
       cW * ((cE - &1) * (cE + sE) + &13 / &50 * sE pow 2) +
       r * ((cE - &1) * (cE - sE) + &13 / &50 * cE * sE)`;
      `&0 < cW * --((cE - &1) * (cE + sE) + &13 / &50 * sE pow 2)`;
      `&0 <= r * (&7 / &100 - ((cE - &1) * (cE - sE) + &13 / &50 * cE * sE))`;
      `r <= cW`; `cW <= &1`] THEN
    REAL_ARITH_TAC;
    (* floor *)
    OCPESU_PROD `&0 <= (sE * cW + cE * r) * (sE * uE + cE * vE + &1)` THEN
    OCPESU_PROD `&0 <= cW * (cE - (uE + aE))` THEN
    OCPESU_PROD `&0 < cE * (sE * cW + cE * r)` THEN
    OCPESU_PROD `&0 < (aE - &1) * (cW + cE * (sE * cW + cE * r))` THEN
    OCPESU_FACT `cE * ABT_lower cE sE uE vE aE cW (--r) <
                 (&1 - cE) * ((sE * cW + cE * r) - cW)`
     (ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`&0 <= (sE * cW + cE * r) * (sE * uE + cE * vE + &1)`;
        `&0 <= cW * (cE - (uE + aE))`;
        `&0 < (aE - &1) * (cW + cE * (sE * cW + cE * r))`] THEN
      SUBGOAL_THEN `cW * uE * (cE * cE + sE * sE) = cW * uE` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
      REAL_ARITH_TAC) THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `cW:real`; `r:real`] OCPES_FLOOR_NORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    OCPESU_FACT `&0 < cE` RASM_ARITH_TAC THEN
    OCPESU_FACT `ABT_lower cE sE uE vE aE cW (--r) < &1 - cW`
     (MATCH_MP_TAC OCPESU_CANCEL THEN EXISTS_TAC `cE:real` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`cE * ABT_lower cE sE uE vE aE cW (--r) < (&1 - cE) * ((sE * cW + cE * r) - cW)`;
        `(&1 - cE) * (sE * cW + cE * r - cW) < cE * (&1 - cW)`] THEN
      REAL_ARITH_TAC) THEN
    OCPESU_PROD `&0 <= cE * (cW - r)` THEN
    OCPESU_PROD `&0 <= cW * (&3 / &7 - (cE + sE - &1))` THEN
    OCPESU_FACT `(sE * cW + cE * r) - cW < &1 / &2`
     (OCPESU_USE [`&0 <= cE * (cW - r)`; `&0 <= cW * (&3 / &7 - (cE + sE - &1))`; `cW <= &1`]) THEN
    OCPESU_PROD `&0 <= (&1 - cE) * (&1 / &2 - ((sE * cW + cE * r) - cW))` THEN
    OCPESU_FACT `ABT_lower cE sE uE vE aE cW (--r) < &1 / &18`
     (MATCH_MP_TAC OCPESU_CANCEL THEN EXISTS_TAC `cE:real` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`cE * ABT_lower cE sE uE vE aE cW (--r) < (&1 - cE) * ((sE * cW + cE * r) - cW)`;
        `&0 <= (&1 - cE) * (&1 / &2 - ((sE * cW + cE * r) - cW))`; `&113 / &125 < cE`] THEN
      REAL_ARITH_TAC) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]);;

(* Lean: negative_w_axis *)
let OCPESU_NEGATIVE_W_AXIS = prove
 (`forall cW sW uW vW aW cE sE uE vE aE r.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     sW = --r /\ &0 < cW /\ &0 <= r /\ r <= cW /\ &1 < aW /\ aW <= &1001 / &1000 /\
     ocpef_data cE sE uE vE aE /\
     linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\ linside cW sW uW vW aW (&0) (&0) /\
     (forall y. &0 <= y ==> y <= &4 / &5 ==> ~linside cW sW uW vW aW (--(&1)) y) /\
     ABT_upper cW sW uW vW aW cW sW <= ABT_lower cE sE uE vE aE cW sW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `r:real`]
    OCPESU_NEGATIVE_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `r:real`] OCPEW_NEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ABT_upper cW sW uW vW aW cW sW <= ABT_lower cE sE uE vE aE cW sW` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN RASM_ARITH_TAC);;

(* Lean: positive_w_axis *)
let OCPESU_POSITIVE_W_AXIS = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &0 < cW /\ &0 <= sW /\ sW <= cW /\ &1 < aW /\ aW <= &1001 / &1000 /\
     ocpef_data cE sE uE vE aE /\
     linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\ linside cW sW uW vW aW (&0) (&0) /\
     ~linside cW sW uW vW aW (&0) (--(C1092WPS_half cE sE)) /\
     (forall y. &0 <= y ==> y <= &4 / &5 ==> ~linside cW sW uW vW aW (--(&1)) y) /\
     ABT_upper cW sW uW vW aW sW (--cW) <= ABT_lower cE sE uE vE aE sW (--cW)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCPESU_DATA_TAC THEN
  OCPESU_FACT `&0 < cE` RASM_ARITH_TAC THEN
  OCPESU_PROD `&0 < cE * cW` THEN
  OCPESU_PROD `&0 <= sE * sW` THEN
  OCPESU_FACT `&0 < cE * cW + sE * sW` (OCPESU_USE [`&0 < cE * cW`; `&0 <= sE * sW`]) THEN
  OCPESU_FACT `(cE * cW + sE * sW) pow 2 + (cE * sW - sE * cW) pow 2 = &1`
   (SUBGOAL_THEN `(cE * cW + sE * sW) pow 2 + (cE * sW - sE * cW) pow 2 =
                  (cE * cE + sE * sE) * (cW * cW + sW * sW)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_LID]]) THEN
  OCPESU_FACT `cE * cW + sE * sW <= &1`
   (MP_TAC(SPEC `cE * sW - sE * cW` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `(cE * cW + sE * sW) - &1` REAL_LE_POW_2) THEN
    UNDISCH_TAC `(cE * cW + sE * sW) pow 2 + (cE * sW - sE * cW) pow 2 = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `C1092WPS_half cE sE`]
    OCPEW_POSITIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `--sW`; `cW:real`]
    OCWPVG_UPPER_NEG) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN STRIP_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `ABT_upper cW sW uW vW aW sW (--cW) <= ABT_lower cE sE uE vE aE sW (--cW)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OCPESU_FACT `cE pow 2 + sE pow 2 = &1` (ASM_REWRITE_TAC[REAL_POW_2]) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* face *)
    OCPESU_FACT `&1 - cE - &13 / &50 * sE < vE + aE` RASM_ARITH_TAC THEN
    OCPESU_PROD `&0 < (cE * cW + sE * sW) * ((vE + aE) - (&1 - cE - &13 / &50 * sE))` THEN
    OCPESU_FACT `ABT_lower cE sE uE vE aE sW (--cW) <
                 --(cE * cW + sE * sW) * (&1 - cE - &13 / &50 * sE)`
     (ASM_CASES_TAC `&0 <= cE * sW - sE * cW` THENL
       [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `sW:real`; `--cW`]
          OCSB_LOWER_PN) THEN
        ANTS_TAC THENL
         [CONJ_TAC THEN MAP_EVERY (MP_TAC o ASSUME)
            [`&0 <= cE * sW - sE * cW`; `&0 < cE * cW + sE * sW`] THEN REAL_ARITH_TAC;
          DISCH_THEN SUBST1_TAC] THEN
        OCPESU_FACT `uE < &0` RASM_ARITH_TAC THEN
        OCPESU_PROD `&0 <= (cE * sW - sE * cW) * --uE` THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`&0 <= (cE * sW - sE * cW) * --uE`;
          `&0 < (cE * cW + sE * sW) * ((vE + aE) - (&1 - cE - &13 / &50 * sE))`] THEN
        REAL_ARITH_TAC;
        MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `sW:real`; `--cW`]
          OCSB_LOWER_NN) THEN
        ANTS_TAC THENL
         [CONJ_TAC THEN MAP_EVERY (MP_TAC o ASSUME)
            [`~(&0 <= cE * sW - sE * cW)`; `&0 < cE * cW + sE * sW`] THEN REAL_ARITH_TAC;
          DISCH_THEN SUBST1_TAC] THEN
        OCPESU_FACT `&0 <= sE * cW - cE * sW` RASM_ARITH_TAC THEN
        OCPESU_PROD `&0 <= (sE * cW - cE * sW) * (uE + aE)` THEN
        MAP_EVERY (MP_TAC o ASSUME)
         [`&0 <= (sE * cW - cE * sW) * (uE + aE)`;
          `&0 < (cE * cW + sE * sW) * ((vE + aE) - (&1 - cE - &13 / &50 * sE))`] THEN
        REAL_ARITH_TAC]) THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`] OCISS_PROJECTION_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_CASES_TAC `&0 <= &1 - cE - &13 / &50 * sE` THENL
     [OCPESU_PROD `&0 <= (cE * cW + sE * sW) * (&1 - cE - &13 / &50 * sE)` THEN RASM_ARITH_TAC;
      OCPESU_PROD `&0 <= (&1 - (cE * cW + sE * sW)) * --(&1 - cE - &13 / &50 * sE)` THEN
      RASM_ARITH_TAC];
    (* floor *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `sW:real`; `--cW`]
      OCSB_LOWER_BOUND_PN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < cE * cW + sE * sW` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    OCPESU_PROD `&0 <= cE * ((sW * cE + --cW * sE) * uE + (--sW * sE + --cW * cE) * (vE + aE) -
                             ABT_lower cE sE uE vE aE sW (--cW))` THEN
    OCPESU_PROD `&0 <= (cE * cW + sE * sW) * (sE * uE + cE * vE + &1)` THEN
    OCPESU_PROD `&0 <= sW * (cE - (uE + aE))` THEN
    OCPESU_PROD `&0 < cE * (cE * cW + sE * sW)` THEN
    OCPESU_PROD `&0 < (aE - &1) * (sW + cE * (cE * cW + sE * sW))` THEN
    OCPESU_FACT `cE * ABT_lower cE sE uE vE aE sW (--cW) <
                 (&1 - cE) * ((cE * cW + sE * sW) - sW)`
     (MAP_EVERY (MP_TAC o ASSUME)
       [`&0 <= cE * ((sW * cE + --cW * sE) * uE + (--sW * sE + --cW * cE) * (vE + aE) -
                     ABT_lower cE sE uE vE aE sW (--cW))`;
        `&0 <= (cE * cW + sE * sW) * (sE * uE + cE * vE + &1)`;
        `&0 <= sW * (cE - (uE + aE))`;
        `&0 < (aE - &1) * (sW + cE * (cE * cW + sE * sW))`] THEN
      SUBGOAL_THEN `sW * uE * (cE * cE + sE * sE) = sW * uE` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
      REAL_ARITH_TAC) THEN
    OCPESU_FACT `sW < &1`
     (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      OCPESU_PROD `&0 <= (sW - &1) * (sW + &1)` THEN
      OCPESU_PROD `&0 < cW * cW` THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`&0 <= (sW - &1) * (sW + &1)`; `&0 < cW * cW`; `cW * cW + sW * sW = &1`] THEN
      REAL_ARITH_TAC) THEN
    OCPESU_PROD `&0 <= (&1 - cE) * (&1 - (cE * cW + sE * sW))` THEN
    OCPESU_PROD `&0 < (&1 - sW) * (&12 / &113 * cE - (&1 - cE))` THEN
    OCPESU_FACT `ABT_lower cE sE uE vE aE sW (--cW) < &12 / &113 * (&1 - sW)`
     (MATCH_MP_TAC OCPESU_CANCEL THEN EXISTS_TAC `cE:real` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`cE * ABT_lower cE sE uE vE aE sW (--cW) < (&1 - cE) * ((cE * cW + sE * sW) - sW)`;
        `&0 <= (&1 - cE) * (&1 - (cE * cW + sE * sW))`;
        `&0 < (&1 - sW) * (&12 / &113 * cE - (&1 - cE))`] THEN
      REAL_ARITH_TAC) THEN
    RASM_ARITH_TAC]);;
