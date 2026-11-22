(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerLongitudinal.lean                *)
(* (namespace N12Compact.CornerWallMarkerLongitudinal).                      *)
(* Positive-L longitudinal support using both genuine foreign markers.       *)
(* Squares are 5-tuples; Lean upper/lower are ABT_upper/ABT_lower; bottom is *)
(* cwcb_bottom; CornerWallPositiveLongitudinal.incoming is CWPL_INCOMING;    *)
(* CornerWallSharedAxis.bottom_support is CWSA_BOTTOM_SUPPORT.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallCycleBounds.ml";;
needs "n12/geometry/CornerWallSharedAxis.ml";;
needs "n12/geometry/CornerWallPositiveLongitudinal.ml";;
needs "n12/geometry/NegativeWallMarkerCap.ml";;

let CWML_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: X (def) *)
let CWML_X_DEF = new_definition
 `cwml_x (d:real) (t:real) = &3 - (&13 / &20) * t pow 2 - (&92 / &125) * d * t + t - d`;;

(* Lean: Y (def) *)
let CWML_Y_DEF = new_definition
 `cwml_y (d:real) (t:real) = &33 / &20 - (&92 / &125) * t pow 2 + (&13 / &20) * d * t - d - t`;;

(* Lean: H (def) *)
let CWML_H_DEF = new_definition
 `cwml_h (d:real) (t:real) (l:real) (r:real) = l * d - r * t + l * t + r * d`;;

(* Lean: h_nonnegative *)
let CWML_H_NONNEGATIVE = prove
 (`forall d t l r. c977cc_normal d t /\ c977cc_normal l r ==> &0 <= cwml_h d t l r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN REWRITE_TAC[CWML_H_DEF] THEN
  NLIN_FACTS_TAC [] [`&0 <= d * (l - r)`; `&0 <= r * (d - t)`; `&0 <= l * t`; `&0 <= r * d`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: marker_support *)
let CWML_MARKER_SUPPORT = prove
 (`forall cW sW uW vW aW t l r.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cW t /\ c977cc_normal l r /\ sW = --t /\
     uW + aW <= (&33 / &20) * cW - (&47 / &20) * t /\
     vW + aW <= (&457 / &500) * t + &3 * cW
     ==> ABT_lower cW sW uW vW aW l r + (aW - &1) * cwml_h cW t l r <=
         l * cwml_y cW t + r * cwml_x cW t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= cW * (l - r)`; `&0 <= r * (cW - t)`; `&0 <= l * cW - r * t`;
                     `&0 <= l * t + r * cW`] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `l:real`; `r:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[CWML_X_DEF; CWML_Y_DEF; CWML_H_DEF] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (l * cW - r * t) * (((&33 / &20) * cW - (&47 / &20) * t) - (uW + aW))`;
    `&0 <= (l * t + r * cW) * (((&457 / &500) * t + &3 * cW) - (vW + aW))`] THEN
  NLIN_TAC ~deg2:false
   [CWML_EQ_HINT `(&33 / &20) * l + &3 * r` (ASSUME `cW pow 2 + t pow 2 = &1`)]);;

(* Lean: bottom_axis_of_margin *)
let CWML_BOTTOM_AXIS_OF_MARGIN = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cW t /\
     sW = --t /\ &1 < aL /\ aL = aW /\ lcont cL sL uL vL aL /\
     cwcb_bottom cO sO < vO + aO /\
     uW + aW <= (&33 / &20) * cW - (&47 / &20) * t /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     uL + aL <= ABT_lower cW sW uW vW aW cL sL /\
     &0 <= &1 + (sL / cO) * cwcb_bottom cO sO + (sL / cO) * (cO * cL + sO * sL) -
           cL * cwml_y cW t - sL * cwml_x cW t
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] CWPL_INCOMING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `sL:real`] CWML_MARKER_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `t:real`; `cL:real`; `sL:real`] CWML_H_NONNEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(cO = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `cO * (&1 + (sL / cO) * cwcb_bottom cO sO + (sL / cO) * (cO * cL + sO * sL) -
          cL * cwml_y cW t - sL * cwml_x cW t) =
    sL * cwcb_bottom cO sO + (cO + sL * (cO * cL + sO * sL) + cO * cwml_h cW t cL sL) -
    cO * (cL * cwml_y cW t + sL * cwml_x cW t + cwml_h cW t cL sL)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(cO = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cO * cL`; `&0 <= sO * sL`; `&0 <= cL * t`; `&0 <= sL * cW`;
    `&0 <= cO * (ABT_lower cW sW uW vW aL cL sL - (uL + aL))`;
    `&0 <= cO * ((cL * cwml_y cW t + sL * cwml_x cW t) -
                 (ABT_lower cW sW uW vW aL cL sL + (aL - &1) * cwml_h cW t cL sL))`;
    `&0 <= cO * (&1 + (sL / cO) * cwcb_bottom cO sO + (sL / cO) * (cO * cL + sO * sL) -
           cL * cwml_y cW t - sL * cwml_x cW t)`;
    `&0 <= sL * ((vO + aO) - cwcb_bottom cO sO)`;
    `&0 <= sL * (cO * cL + sO * sL)`; `&0 <= cO * cwml_h cW t cL sL`;
    `&0 < cO + sL * (cO * cL + sO * sL) + cO * cwml_h cW t cL sL`;
    `&0 < (aL - &1) * (cO + sL * (cO * cL + sO * sL) + cO * cwml_h cW t cL sL)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: singleton_axis_of_margin *)
let CWML_SINGLETON_AXIS_OF_MARGIN = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cW t /\
     sW = --t /\ &1 < aL /\ aO = aL /\ aL = aW /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO + sO /\
     uW + aW <= (&33 / &20) * cW - (&47 / &20) * t /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     ABT_upper cO sO uO vO aO (--sL) cL <= vL /\
     uL + aL <= ABT_lower cW sW uW vW aW cL sL /\
     &0 <= cO * cL + cO * sL + cO * sL * (cO * cL + sO * sL) + sL pow 2 -
           sL pow 2 * (&2 * cO + sO) - cO * cL * (cL * cwml_y cW t + sL * cwml_x cW t)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cL:real`; `sL:real`]
    CWSA_BOTTOM_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                  DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `sL:real`] CWML_MARKER_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `t:real`; `cL:real`; `sL:real`] CWML_H_NONNEGATIVE) THEN
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
            cO * cL * cwml_h cW t cL sL`
  and rc = `sL pow 2 * (&2 * cO + sO) +
            cO * cL * (cL * cwml_y cW t + sL * cwml_x cW t + cwml_h cW t cL sL)` in
  let sub tm = subst [qc,`QC:real`; rc,`RC:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= cL * uL - sL * (vL + aL)`;
    `&0 <= sL * (cO * ABT_upper cO sO uO vO aL (--sL) cL -
                 (aL * (cO * (cO * cL + sO * sL) + sL) - sL * (&2 * cO + sO)))`;
    `&0 <= cO * sL`; `&0 <= (cO * sL) * (vL - ABT_upper cO sO uO vO aL (--sL) cL)`;
    `&0 <= cO * (cL * uL - sL * (vL + aL))`;
    `&0 <= cO * cL`;
    `&0 <= (cO * cL) * ((cL * cwml_y cW t + sL * cwml_x cW t) -
                 (ABT_lower cW sW uW vW aL cL sL + (aL - &1) * cwml_h cW t cL sL))`;
    `&0 <= (cO * cL) * (ABT_lower cW sW uW vW aL cL sL - (uL + aL))`;
    `aL * QC <= RC`;
    `&0 <= sO * sL`; `&0 <= cL * t`; `&0 <= sL * cW`;
    `&0 < QC`; `&0 < (aL - &1) * QC`]) THEN
  NLIN_TAC ~deg2:false []);;
