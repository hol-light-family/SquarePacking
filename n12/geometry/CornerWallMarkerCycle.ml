(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerCycle.lean                       *)
(* (namespace N12Compact.CornerWallMarkerCycle).                             *)
(* Actual-square negative-wall cycle with genuine marker faces.  Squares    *)
(* O, L, W are cO sO uO vO aO etc.; Data is the predicate cwmcy_data.        *)
(* lower/upper are ABT_lower/ABT_upper, Normal is c977cc_normal, bottom is  *)
(* cwcb_bottom, CornerWallMarkerMixedBounds.boundary is cwmmb_boundary.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CornerSingletonPair.ml";;
needs "n12/geometry/LeftSingletonWallSeparation.ml";;
needs "n12/geometry/CornerWallCycle.ml";;
needs "n12/geometry/CornerWallMarkerShared.ml";;
needs "n12/geometry/CornerWallMarkerMixed.ml";;
needs "n12/geometry/CornerWallMarkerOtherMixed.ml";;
needs "n12/geometry/CornerWallMarkerLongitudinal.ml";;
needs "n12/geometry/CornerWallMarkerLongitudinalBounds.ml";;
needs "n12/geometry/CornerWallMarkerNegativeLarge.ml";;
needs "n12/geometry/CornerWallMarkerNegativeMixed.ml";;

(* Lean: Data (structure) *)
let cwmcy_data = new_definition
 `cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW (t:real) <=>
    c977cc_normal cO sO /\ &0 < cL /\ abs sL <= cL /\
    c977cc_normal cW t /\ sW = --t /\ &1 < aL /\ aO = aL /\ aL = aW /\
    lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
    linside cO sO uO vO aO (&1) (&457 / &500) /\
    linside cO sO uO vO aO (&28 / &25) (&1) /\
    linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
    linside cL sL uL vL aL (&457 / &500) (&1) /\
    linside cL sL uL vL aL (&1) (&1) /\
    linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
    linside cW sW uW vW aW (&457 / &500) (&2) /\
    uO + aO <= &2 * cO + (&457 / &500) * sO /\
    cwmmb_boundary cO sO < vO + aO /\
    uW + aW <= (&33 / &20) * cW - (&47 / &20) * t /\
    vW + aW <= (&457 / &500) * t + &3 * cW /\
    sO <= t /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
    ldisj cO sO uO vO aO cL sL uL vL aL /\
    ldisj cL sL uL vL aL cW sW uW vW aW`;;

let CWMCY_DATA_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[cwmcy_data] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cO sO`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cW t`));;

let CWMCY_CLOSE_TAC =
  REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);;

let CWMCY_SUBST_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(sW:real) = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(aL:real) = aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(aO:real) = aL`));;

(* Lean: positive_normal *)
let CWMCY_POSITIVE_NORMAL = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cL * cL + sL * sL = &1 /\
     cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t /\ &0 <= sL
     ==> c977cc_normal cL sL`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cwmcy_data; c977cc_normal] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `abs sL <= cL` THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `cL * cL + sL * sL = &1` THEN REAL_ARITH_TAC]);;

(* Lean: negative_normal *)
let CWMCY_NEGATIVE_NORMAL = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cL * cL + sL * sL = &1 /\
     cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t /\ sL <= &0
     ==> c977cc_normal cL (--sL)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cwmcy_data; c977cc_normal] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `abs sL <= cL` THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `cL * cL + sL * sL = &1` THEN REAL_ARITH_TAC]);;

(* Lean: bottom_choices *)
let CWMCY_BOTTOM_CHOICES = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW (uW:real) vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t
     ==> vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO \/
         (&0 <= sL /\ ABT_upper cO sO uO vO aO (--sL) cL <= vL) \/
         (sL < &0 /\ uL + aL <= ABT_lower cO sO uO vO aO cL sL)`,
  CWMCY_DATA_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
    CSP_ALTERNATIVES) THEN
  ANTS_TAC THENL [CWMCY_CLOSE_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[CSP_directed] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: wall_choices *)
let CWMCY_WALL_CHOICES = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW t.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t
     ==> (cL / &4 < sL /\ uL + aL <= ABT_lower cW sW uW vW aW cL sL) \/
         vL + aL <= ABT_lower cW sW uW vW aW (--sL) cL \/
         ABT_upper cL sL uL vL aL t cW <= vW`,
  CWMCY_DATA_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    LSWS_NEGATIVE_WALL_ALTERNATIVES) THEN
  ANTS_TAC THENL [CWMCY_CLOSE_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

(* Lean: relaxed_bottom *)
let CWMCY_RELAXED_BOTTOM = prove
 (`forall cO sO (uO:real) vO aO (cL:real) (sL:real) (uL:real) (vL:real) (aL:real)
    (cW:real) (sW:real) (uW:real) (vW:real) (aW:real) t.
     cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t
     ==> cwcb_bottom cO sO < vO + aO`,
  CWMCY_DATA_TAC THEN
  SUBGOAL_THEN `&0 < cO` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&43 / &500) * sO pow 2 / cO` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `cwmmb_boundary cO sO = cwcb_bottom cO sO + (&43 / &500) * sO pow 2 / cO`
    ASSUME_TAC THENL
   [REWRITE_TAC[CWMMB_BOUNDARY_DEF; CWCB_BOTTOM_DEF] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CWMCY_CHOICES_TAC =
  MAP_EVERY (fun th ->
    MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`] th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC)
   [CWMCY_RELAXED_BOTTOM; CWMCY_WALL_CHOICES; CWMCY_BOTTOM_CHOICES];;

let CWMCY_CASES_TAC =
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)));;

let CWMCY_SPEC_ALL th =
  SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aL:real`;
         `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
         `cW:real`; `--t`; `uW:real`; `vW:real`; `aL:real`] th;;

(* Lean: positive *)
let CWMCY_POSITIVE = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t /\ &0 <= sL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    CWMCY_POSITIVE_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CWMCY_CHOICES_TAC THEN
  UNDISCH_TAC `cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t` THEN
  REWRITE_TAC[cwmcy_data] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cO sO`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cW t`)) THEN
  CWMCY_SUBST_TAC THEN
  SUBGOAL_THEN `vW + aL <= t + &3 * cW /\ uO + aL <= &2 * cO + sO`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWMCY_CASES_TAC THEN
  FIRST [RASM_ARITH_TAC;
    MATCH_MP_TAC(SPEC `t:real` (CWMCY_SPEC_ALL CWMM_SECTOR)) THEN CWMCY_CLOSE_TAC;
    MATCH_MP_TAC(SPEC `t:real` (CWMCY_SPEC_ALL CWC_TRANSVERSE_SECTOR)) THEN
      CWMCY_CLOSE_TAC;
    MATCH_MP_TAC(SPEC `t:real` (CWMCY_SPEC_ALL CWMS_SECTOR)) THEN CWMCY_CLOSE_TAC;
    MATCH_MP_TAC(SPEC `t:real` (CWMCY_SPEC_ALL CWMOM_SECTOR)) THEN CWMCY_CLOSE_TAC;
    MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `sL:real`]
      CWMLB_BOTTOM_AXIS) THEN
    ANTS_TAC THENL [CWMCY_CLOSE_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC(SPEC `t:real` (CWMCY_SPEC_ALL CWML_BOTTOM_AXIS_OF_MARGIN)) THEN
    CWMCY_CLOSE_TAC;
    MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `sL:real`]
      CWMLB_SINGLETON_AXIS) THEN
    ANTS_TAC THENL [CWMCY_CLOSE_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC(SPEC `t:real` (CWMCY_SPEC_ALL CWML_SINGLETON_AXIS_OF_MARGIN)) THEN
    CWMCY_CLOSE_TAC]);;

(* Lean: negative_backward *)
let CWMCY_NEGATIVE_BACKWARD = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t /\ sL <= &0 /\
     uL + aL <= ABT_lower cO sO uO vO aO cL sL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    CWMCY_NEGATIVE_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    CWMCY_WALL_CHOICES) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t` THEN
  REWRITE_TAC[cwmcy_data] THEN STRIP_TAC THEN
  CWMCY_SUBST_TAC THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `&0 < cL / &4` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(SPECL [`--sL`; `t:real`] (CWMCY_SPEC_ALL CWMNL_LEFT_AXIS)) THEN
    CWMCY_CLOSE_TAC;
    MATCH_MP_TAC(SPECL [`--sL`; `t:real`] (CWMCY_SPEC_ALL CWMNL_WALL_AXIS)) THEN
    CWMCY_CLOSE_TAC]);;

(* Lean: negative *)
let CWMCY_NEGATIVE = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t /\ sL < &0
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    CWMCY_NEGATIVE_NORMAL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(uL + aL <= ABT_lower cO sO uO vO aO cL sL)` ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC CWMCY_NEGATIVE_BACKWARD THEN
    MAP_EVERY EXISTS_TAC [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
      `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
      `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  CWMCY_CHOICES_TAC THEN
  UNDISCH_TAC `cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t` THEN
  REWRITE_TAC[cwmcy_data] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cW t`)) THEN
  CWMCY_SUBST_TAC THEN
  SUBGOAL_THEN `vW + aL <= t + &3 * cW /\ &0 < cL / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWMCY_CASES_TAC THEN
  FIRST [RASM_ARITH_TAC;
    ASM_MESON_TAC[];
    MATCH_MP_TAC(SPECL [`--sL`; `t:real`] (CWMCY_SPEC_ALL CWMNM_SECTOR)) THEN
      CWMCY_CLOSE_TAC;
    MATCH_MP_TAC(SPEC `t:real` (CWMCY_SPEC_ALL CWC_TRANSVERSE_SECTOR)) THEN
      CWMCY_CLOSE_TAC]);;

(* Lean: impossible *)
let CWMCY_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     cwmcy_data cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 <= sL \/ sL < &0`) THENL
   [MATCH_MP_TAC CWMCY_POSITIVE; MATCH_MP_TAC CWMCY_NEGATIVE] THEN
  MAP_EVERY EXISTS_TAC [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
    `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`] THEN
  ASM_REWRITE_TAC[]);;
