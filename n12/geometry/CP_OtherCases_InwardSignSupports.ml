(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/InwardSignSupports.lean             *)
(* (namespace N12Compact.Completion.OtherCases.InwardSignSupports).  Full   *)
(* support obstructions for a nonnegative inward southeast square.          *)
(* Squares W = cW sW uW vW aW, E = cE sE uE vE aE.  upper / lower /         *)
(* strict_bounds: ABT_upper / ABT_lower / ABT_STRICT_BOUNDS; SupportBands.  *)
(* lower_pn / lower_nn / lower_bound_pn: OCSB_*; InwardSignScalars.*:       *)
(* OCISS_*; CanonicalScalars.bounds: CCCS_BOUNDS.                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_BottomBarSupport.ml";;
needs "n12/geometry/CP_OtherCases_SupportBands.ml";;
needs "n12/geometry/CP_OtherCases_InwardSignScalars.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

(* Lean: Data (structure) *)
let ocisup_data = new_definition
 `ocisup_data (c:real) s u v a <=>
    &0 < c /\ &0 < s /\ s <= c /\ &1 < a /\
    u + a <= c - &13 / &50 * s /\ v + a <= &0 /\
    (--(&13 / &50) * s - c <= v \/ --(&1) <= s * u + c * v)`;;

let OCISUP_SETUP_TAC =
  REWRITE_TAC[IMP_CONJ; ocisup_data] THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then
    STRIP_ASSUME_TAC th else NO_TAC)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `cE pow 2 + sE pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC];;

let OCISUP_PROD_TAC tms =
  SUBGOAL_THEN (list_mk_conj tms) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: own_axis *)
let OCISUP_OWN_AXIS = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      ocisup_data cE sE uE vE aE /\
      linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
      ABT_upper cW sW uW vW aW sE (--cE) <= ABT_lower cE sE uE vE aE sE (--cE)
      ==> false`,
  REPEAT GEN_TAC THEN OCISUP_SETUP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `--(&7 / &20)`; `--(&7 / &20)`; `sE:real`; `--cE`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `ABT_lower cE sE uE vE aE sE (--cE) = --(vE + aE)` ASSUME_TAC THENL
   [REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
    SUBGOAL_THEN `abs(sE * cE + --cE * sE) = &0 /\ abs(--sE * sE + --cE * cE) = &1`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_ARITH `sE * cE + --cE * sE = &0`] THEN
      ASM_REWRITE_TAC[REAL_ARITH `--sE * sE + --cE * cE = --(cE * cE + sE * sE)`] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`] OCISS_PROJECTION_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`] OCISS_SHORT_ARC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REAL_ARITH_TAC;
    OCISUP_PROD_TAC
     [`&0 <= sE * ((cE - &13 / &50 * sE) - (uE + aE))`;
      `&0 < cE * (--(&7 / &20) * (cE - sE) - (vE + aE))`;
      `&0 < (aE - &1) * (cE + sE)`;
      `&0 <= (cE - sE) * (&29 / &100 * cE - &13 / &50 * sE)`;
      `&0 <= cE * cE`] THEN
    RASM_ARITH_TAC]);;

(* Lean: negative_w_axis (stated with sW = --r) *)
let OCISUP_NEGATIVE_W_AXIS = prove
 (`forall cW sW uW vW aW cE sE uE vE aE r.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      sW = --r /\ &0 < cW /\ &0 <= r /\ r <= cW /\
      ocisup_data cE sE uE vE aE /\
      linside cW sW uW vW aW (&0) (&0) /\
      ABT_upper cW sW uW vW aW cW sW <= ABT_lower cE sE uE vE aE cW sW
      ==> false`,
  REPEAT GEN_TAC THEN OCISUP_SETUP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --r`)) THEN
  MP_TAC(SPECL [`cW:real`; `--r`; `uW:real`; `vW:real`; `aW:real`;
                `&0`; `&0`; `cW:real`; `--r`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  OCISUP_PROD_TAC [`&0 <= cW * (cE - sE)`; `&0 <= sE * (cW - r)`;
                   `&0 < sE * cW`; `&0 <= cE * r`] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `cW:real`; `--r`]
    OCSB_LOWER_PN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < (cE * cW - sE * r) * uE - (sE * cW + cE * r) * (vE + aE)`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [OCISUP_PROD_TAC
     [`&0 <= (cE * cW - sE * r) * ((cE - &13 / &50 * sE) - (uE + aE))`;
      `&0 <= (sE * cW + cE * r) * (vE + cE + &13 / &50 * sE)`;
      `&0 < (aE - &1) * ((cE * cW - sE * r) + (sE * cW + cE * r))`] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `cW:real`; `r:real`] OCISS_NEGATIVE_BAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    RASM_ARITH_TAC;
    OCISUP_PROD_TAC [`&0 < (sE * cW + cE * r) * cE`; `&0 <= cE * (cW - r)`] THEN
    OCISUP_PROD_TAC
     [`&0 <= (sE * cW + cE * r) * (sE * uE + cE * vE + &1)`;
      `&0 <= cW * ((cE - &13 / &50 * sE) - (uE + aE))`;
      `&0 < (aE - &1) * (cW + (sE * cW + cE * r) * cE)`;
      `&0 <= (&1 - cE) * (cE * (cW - r))`;
      `&0 < cE * ((cE * cW - sE * r) * uE - (sE * cW + cE * r) * (vE + aE))`] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`] OCISS_X_NEGATIVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < cW * --((&1 - cE) * (cE + sE - &1) - &13 / &50 * sE)` ASSUME_TAC
      THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `cE * ((cE * cW - sE * r) * uE - (sE * cW + cE * r) * (vE + aE)) +
      (sE * cW + cE * r) * (sE * uE + cE * vE + &1) +
      cW * ((cE - &13 / &50 * sE) - (uE + aE)) +
      (aE - &1) * (cW + (sE * cW + cE * r) * cE) + (&1 - cE) * (cE * (cW - r)) =
      cW * ((&1 - cE) * (cE + sE - &1) - &13 / &50 * sE)` ASSUME_TAC THENL
     [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]);;

(* Lean: positive_w_axis *)
let OCISUP_POSITIVE_W_AXIS = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      &0 < cW /\ &0 <= sW /\ sW <= cW /\
      ocisup_data cE sE uE vE aE /\
      linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
      linside cE sE uE vE aE (&13 / &50) (&0) /\
      ABT_upper cW sW uW vW aW sW (--cW) <= ABT_lower cE sE uE vE aE sW (--cW)
      ==> false`,
  REPEAT GEN_TAC THEN OCISUP_SETUP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `--(&7 / &20)`; `--(&7 / &20)`; `sW:real`; `--cW`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  OCISUP_PROD_TAC [`&0 < cE * cW`; `&0 <= sE * sW`] THEN
  SUBGOAL_THEN `&7 / &20 * (cW - sW) < ABT_lower cE sE uE vE aE sW (--cW)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [ASM_CASES_TAC `&0 <= cE * sW - sE * cW` THENL
     [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `sW:real`; `--cW`]
        OCSB_LOWER_PN) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      OCISUP_PROD_TAC
       [`&0 <= (cE * sW - sE * cW) * ((cE - &13 / &50 * sE) - (uE + aE))`;
        `&0 <= (cE * cW + sE * sW) * (vE + cE + &13 / &50 * sE)`;
        `&0 < (aE - &1) * ((cE * sW - sE * cW) + (cE * cW + sE * sW))`] THEN
      MP_TAC(SPECL [`cE:real`; `sE:real`; `cW:real`; `sW:real`] OCISS_POSITIVE_BAR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
      RASM_ARITH_TAC;
      MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `sW:real`; `--cW`]
        OCSB_LOWER_NN) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(SPECL [`cE:real`; `sE:real`] OCISS_PROJECTION_CAP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(SPECL [`cE:real`; `sE:real`] OCISS_SHORT_ARC) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MP_TAC(SPECL [`cE:real`; `sE:real`; `cW:real`; `sW:real`] OCISS_DIFFERENCE_ORDER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `(cE * cW + sE * sW) pow 2 + (cE * sW - sE * cW) pow 2 = &1`
        ASSUME_TAC THENL
       [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
        CONV_TAC REAL_RING; ALL_TAC] THEN
      SUBGOAL_THEN `cE * cW + sE * sW <= &1` ASSUME_TAC THENL
       [MP_TAC(SPEC `cE * sW - sE * cW` REAL_LE_POW_2) THEN
        MP_TAC(SPEC `(cE * cW + sE * sW) - &1` REAL_LE_POW_2) THEN
        UNDISCH_TAC `(cE * cW + sE * sW) pow 2 + (cE * sW - sE * cW) pow 2 = &1` THEN
        SPEC_TAC(`cE * cW + sE * sW`,`k:real`) THEN
        SPEC_TAC(`cE * sW - sE * cW`,`d:real`) THEN
        REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < uE + aE` ASSUME_TAC THENL
       [UNDISCH_TAC `linside cE sE uE vE aE (&13 / &50) (&0)` THEN
        REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      OCISUP_PROD_TAC
       [`&0 <= --(cE * sW - sE * cW) * (uE + aE)`;
        `&0 < (cE * cW + sE * sW) * ((vE + aE) - (&1 - cE - &13 / &50 * sE))`;
        `&0 <= (&1 - (cE * cW + sE * sW)) * (cE + &13 / &50 * sE - &1)`] THEN
      RASM_ARITH_TAC];
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `sW:real`; `--cW`]
      OCSB_LOWER_BOUND_PN) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < (cE * sW - sE * cW) * uE - (cE * cW + sE * sW) * (vE + aE) -
                       &7 / &20 * (cW - sW)` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    OCISUP_PROD_TAC [`&0 < (cE * cW + sE * sW) * cE`] THEN
    OCISUP_PROD_TAC
     [`&0 < cE * ((cE * sW - sE * cW) * uE - (cE * cW + sE * sW) * (vE + aE) -
                  &7 / &20 * (cW - sW))`;
      `&0 <= (cE * cW + sE * sW) * (sE * uE + cE * vE + &1)`;
      `&0 <= sW * ((cE - &13 / &50 * sE) - (uE + aE))`;
      `&0 < (aE - &1) * (sW + (cE * cW + sE * sW) * cE)`] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `cW:real`; `sW:real`] OCISS_POSITIVE_FLOOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `cE * ((cE * sW - sE * cW) * uE - (cE * cW + sE * sW) * (vE + aE) -
            &7 / &20 * (cW - sW)) +
      (cE * cW + sE * sW) * (sE * uE + cE * vE + &1) +
      sW * ((cE - &13 / &50 * sE) - (uE + aE)) +
      (aE - &1) * (sW + (cE * cW + sE * sW) * cE) =
      cW * (cE * (&13 / &20 - cE)) +
      sW * ((&1 - cE) * (sE - &1) - &13 / &50 * sE + &7 / &20 * cE)` ASSUME_TAC THENL
     [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]);;
