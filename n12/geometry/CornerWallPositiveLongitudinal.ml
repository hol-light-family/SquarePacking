(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallPositiveLongitudinal.lean              *)
(* (namespace N12Compact.CornerWallPositiveLongitudinal).                    *)
(* Original-support reduction for positive L's remaining longitudinal       *)
(* separator.  Squares are 5-tuples; Lean upper/lower are ABT_upper/        *)
(* ABT_lower; bottom is cwcb_bottom; left_wall is FSBL_LEFT_WALL;            *)
(* CornerWallSharedAxis.bottom_support is CWSA_BOTTOM_SUPPORT.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallCycleBounds.ml";;
needs "n12/geometry/CornerWallSharedAxis.ml";;

let CWPL_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: X (def) *)
let CWPL_X_DEF = new_definition
 `cwpl_x (d:real) (t:real) = &2 * t pow 2 + (&43 / &500) * d * t + (&72 / &25) * d pow 2 - d`;;

(* Lean: Y (def) *)
let CWPL_Y_DEF = new_definition
 `cwpl_y (d:real) (t:real) = (&457 / &500) * d pow 2 + t pow 2 + (&22 / &25) * d * t - t`;;

(* Lean: marker_support *)
let CWPL_MARKER_SUPPORT = prove
 (`forall cW sW uW vW aW t l r.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cW t /\ c977cc_normal l r /\ sW = --t /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     vW + aW <= t + (&72 / &25) * cW
     ==> ABT_lower cW sW uW vW aW l r + (aW - &1) * (l * t + r * cW) <=
         l * cwpl_y cW t + r * cwpl_x cW t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= cW * (l - r)`; `&0 <= r * (cW - t)`; `&0 <= l * cW - r * t`;
                     `&0 <= l * t + r * cW`] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `l:real`; `r:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `linside cW sW uW vW aW (&457 / &500) (&2)` THEN
  ASM_SIMP_TAC[C977NCO_NEGATIVE_BANDS] THEN STRIP_TAC THEN
  REWRITE_TAC[CWPL_X_DEF; CWPL_Y_DEF] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (l * cW - r * t) * ((cW * &457 / &500 - t * &2) - uW)`;
    `&0 <= (l * t + r * cW) * ((t + (&72 / &25) * cW) - (vW + aW))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: incoming *)
let CWPL_INCOMING = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ lcont cL sL uL vL aL /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO
     ==> sL * (vO + aO) + aL * (cO + sL * (cO * cL + sO * sL)) <= cO * (uL + aL)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN
  SUBGOAL_THEN `abs sL = sL` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; DISCH_TAC] THEN
  UNDISCH_TAC `vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO` THEN
  REWRITE_TAC[C977NCO_LOWER_IN_BANDS; REAL_NEG_NEG] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= cO * cL`; `&0 <= sO * sL`; `&0 <= sO * sL + cO * cL`] THEN
  SUBGOAL_THEN `abs(sO * sL + cO * cL) = sO * sL + cO * cL` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `vO + aO <= (cO * sL - sO * cL) * uL + (cO * cL + sO * sL) * vL`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= aL * (abs(--sO * cL + cO * sL) - (--sO * cL + cO * sL))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      UNDISCH_TAC `vO + aO <= (--sO * cL + cO * sL) * (uL + aL / &2) +
          (sO * sL + cO * cL) * (vL + aL / &2) -
          aL / &2 * (abs(--sO * cL + cO * sL) + (sO * sL + cO * cL))` THEN
      REAL_ARITH_TAC]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cL * uL - sL * (vL + aL)`;
    `&0 <= (cO * cL + sO * sL) * (cL * uL - sL * (vL + aL))`;
    `&0 <= sL * ((cO * sL - sO * cL) * uL + (cO * cL + sO * sL) * vL - (vO + aO))`] THEN
  NLIN_TAC ~deg2:false [CWPL_EQ_HINT `--cO * uL` (ASSUME `cL pow 2 + sL pow 2 = &1`)]);;

(* Lean: bottom_axis_of_margin *)
let CWPL_BOTTOM_AXIS_OF_MARGIN = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cW t /\
     sW = --t /\ &1 < aL /\ aL = aW /\ lcont cL sL uL vL aL /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     cwcb_bottom cO sO < vO + aO /\
     vW + aW <= t + (&72 / &25) * cW /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     uL + aL <= ABT_lower cW sW uW vW aW cL sL /\
     &0 <= &1 + (sL / cO) * cwcb_bottom cO sO + (sL / cO) * (cO * cL + sO * sL) -
           cL * cwpl_y cW t - sL * cwpl_x cW t
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] CWPL_INCOMING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `sL:real`] CWPL_MARKER_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(cO = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `cO * (&1 + (sL / cO) * cwcb_bottom cO sO + (sL / cO) * (cO * cL + sO * sL) -
          cL * cwpl_y cW t - sL * cwpl_x cW t) =
    sL * cwcb_bottom cO sO + (cO + sL * (cO * cL + sO * sL) + cO * (cL * t + sL * cW)) -
    cO * (cL * cwpl_y cW t + sL * cwpl_x cW t + (cL * t + sL * cW))` ASSUME_TAC THENL
   [UNDISCH_TAC `~(cO = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cO * cL`; `&0 <= sO * sL`; `&0 <= cL * t`; `&0 <= sL * cW`;
    `&0 <= cO * (ABT_lower cW sW uW vW aL cL sL - (uL + aL))`;
    `&0 <= cO * ((cL * cwpl_y cW t + sL * cwpl_x cW t) -
                 (ABT_lower cW sW uW vW aL cL sL + (aL - &1) * (cL * t + sL * cW)))`;
    `&0 <= cO * (&1 + (sL / cO) * cwcb_bottom cO sO + (sL / cO) * (cO * cL + sO * sL) -
           cL * cwpl_y cW t - sL * cwpl_x cW t)`;
    `&0 <= sL * ((vO + aO) - cwcb_bottom cO sO)`;
    `&0 <= sL * (cO * cL + sO * sL)`; `&0 <= cO * (cL * t + sL * cW)`;
    `&0 < cO + sL * (cO * cL + sO * sL) + cO * (cL * t + sL * cW)`;
    `&0 < (aL - &1) * (cO + sL * (cO * cL + sO * sL) + cO * (cL * t + sL * cW))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: singleton_axis_of_margin *)
let CWPL_SINGLETON_AXIS_OF_MARGIN = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cW t /\
     sW = --t /\ &1 < aL /\ aO = aL /\ aL = aW /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO + sO /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     vW + aW <= t + (&72 / &25) * cW /\
     ABT_upper cO sO uO vO aO (--sL) cL <= vL /\
     uL + aL <= ABT_lower cW sW uW vW aW cL sL /\
     &0 <= cO * cL + cO * sL + cO * sL * (cO * cL + sO * sL) + sL pow 2 -
           sL pow 2 * (&2 * cO + sO) - cO * cL * (cL * cwpl_y cW t + sL * cwpl_x cW t)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cL:real`; `sL:real`]
    CWSA_BOTTOM_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                  DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `sL:real`] CWPL_MARKER_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                  REWRITE_TAC[lcx] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `abs sL = sL` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  let qc = `cO * cL + cO * sL + sL * (cO * (cO * cL + sO * sL) + sL) +
            cO * cL * (cL * t + sL * cW)`
  and rc = `sL pow 2 * (&2 * cO + sO) +
            cO * cL * (cL * cwpl_y cW t + sL * cwpl_x cW t + (cL * t + sL * cW))` in
  let sub tm = subst [qc,`QC:real`; rc,`RC:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= cL * uL - sL * (vL + aL)`;
    `&0 <= sL * (cO * ABT_upper cO sO uO vO aL (--sL) cL -
                 (aL * (cO * (cO * cL + sO * sL) + sL) - sL * (&2 * cO + sO)))`;
    `&0 <= cO * sL`; `&0 <= (cO * sL) * (vL - ABT_upper cO sO uO vO aL (--sL) cL)`;
    `&0 <= cO * (cL * uL - sL * (vL + aL))`;
    `&0 <= cO * cL`;
    `&0 <= (cO * cL) * ((cL * cwpl_y cW t + sL * cwpl_x cW t) -
                 (ABT_lower cW sW uW vW aL cL sL + (aL - &1) * (cL * t + sL * cW)))`;
    `&0 <= (cO * cL) * (ABT_lower cW sW uW vW aL cL sL - (uL + aL))`;
    `aL * QC <= RC`;
    `&0 <= sO * sL`; `&0 <= cL * t`; `&0 <= sL * cW`;
    `&0 < QC`; `&0 < (aL - &1) * QC`]) THEN
  NLIN_TAC ~deg2:false []);;
