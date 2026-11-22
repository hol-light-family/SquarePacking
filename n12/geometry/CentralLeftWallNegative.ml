(* ========================================================================= *)
(* Port of Compact/Geometry/CentralLeftWallNegative.lean (Jatloe).            *)
(* The central-axis separator is impossible for a negative left-wall square. *)
(* Normal: c977cc_normal; a square W with W.s = -t is cW sW uW vW aW with    *)
(* sW = --t.  LeftWallNegativeFaces: LWNF_*; CentralLeftWallSeparation:      *)
(* CLWS_NEGATIVE_ALTERNATIVES; lower_negative_nonpos:                        *)
(* C977NCO_LOWER_NEGATIVE_NONPOS.                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/LeftWallNegativeFaces.ml";;
needs "n12/geometry/CentralLeftWallSeparation.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

(* Lean: central_tilt *)
let CLWN_CENTRAL_TILT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c s /\ a <= &1001 / &1000 /\
     linside c s u v a (&1) (&2) /\ linside c s u v a (&2) (&3 / &2)
     ==> s < (&4 / &5) * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `s + c / &2 < &1001 / &1000` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  PCT_PROD_TAC `c:real` `s - (&4 / &5) * c` THEN
  PCT_PROD_TAC `c - s:real` `c + s:real` THEN
  PCT_PRODLT_TAC `&1001 / &1000 - (s + c / &2)` `&1001 / &1000 + (s + c / &2)` THEN
  PCT_PRODLT_TAC `c:real` `c:real` THEN
  NLIN_TAC []);;

(* Lean: margin *)
let CLWN_MARGIN = prove
 (`forall C S d t. &0 <= C /\ S <= (&4 / &5) * C /\ &0 <= d /\ d <= &1 /\
             &0 <= t /\ t <= &3 / &5
             ==> &0 <= (&1 - d) * (C - S * d) + C * t * (d - &457 / &500)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCT_PROD_TAC `&1 - d` `d:real` THEN
  PCT_PROD_TAC `(&1 - d) * d` `(&4 / &5) * C - S` THEN
  ASM_CASES_TAC `&457 / &500 <= d` THENL
  [PCT_PROD_TAC `&1 - d` `&1 - (&4 / &5) * d` THEN
   PCT_PROD_TAC `C:real` `(&1 - d) * (&1 - (&4 / &5) * d)` THEN
   PCT_PROD_TAC `C:real` `t:real` THEN
   PCT_PROD_TAC `C * t` `d - &457 / &500` THEN
   RASM_ARITH_TAC;
   PCT_PROD_TAC `&457 / &500 - d` `&3 / &5 - t` THEN
   PCT_PROD_TAC `C:real` `(&457 / &500 - d) * (&3 / &5 - t)` THEN
   MP_TAC(SPECL [`C:real`; `(d - &3 / &4) pow 2`] REAL_LE_MUL) THEN
   ASM_REWRITE_TAC[REAL_LE_POW_2] THEN DISCH_TAC THEN
   SUBGOAL_THEN `C * ((&1 - d) * (&1 - (&4 / &5) * d) + (&3 / &5) * (d - &457 / &500)) =
                 (&4 / &5) * C * (d - &3 / &4) pow 2 + C / &625` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC]);;

(* Lean: not_central_axis *)
let CLWN_NOT_CENTRAL_AXIS = prove
 (`forall cA sA uA vA aA cW sW uW vW aW t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cA sA /\ c977cc_normal cW t /\ sW = --t /\ &1 < aW /\
     aA <= &1001 / &1000 /\
     linside cA sA uA vA aA (&1) (&2) /\ linside cA sA uA vA aA (&2) (&3 / &2) /\
     lcont cW sW uW vW aW /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     ~linside cW sW uW vW aW (&457 / &500) (&3) /\
     ~linside cW sW uW vW aW (&19 / &25) (&187 / &100) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> ~(vA + aA <= ABT_lower cW sW uW vW aW (--sA) cA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --t`)) THEN
  SUBGOAL_THEN `~linside cW (--t) uW vW aW (&1) (&2)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cA sA uA vA aA cW (--t) uW vW aW` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&1`; `&2`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    LWNF_FACES) THEN
  MP_TAC(SPECL [`cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    LWNF_LOWER_FACE_AND_TILT) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CLWN_CENTRAL_TILT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  PCT_NORMAL_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `t:real`] CLWN_MARGIN) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  PCT_PROD_TAC `sA:real` `cW:real` THEN PCT_PROD_TAC `cA:real` `t:real` THEN
  PCT_PROD_TAC `cW:real` `cA - sA:real` THEN PCT_PROD_TAC `sA:real` `cW - t:real` THEN
  SUBGOAL_THEN `&0 <= sA * cW + cA * t /\ &0 <= cA * cW - sA * t` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `sA * cW:real` `cW:real` THEN PCT_PROD_TAC `cA * t:real` `cW:real` THEN
  SUBGOAL_THEN `&0 < cA + sA * cW pow 2 + cA * cW * t` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `--sA`; `cA:real`] C977NCO_LOWER_NEGATIVE_NONPOS) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN RASM_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN `cW * (vA + aA) <=
                cW * ((--sA * cW - cA * t) * (uW + aW) + (--sA * t + cA * cW) * vW)`
  ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `sA * cW + cA * t`
    `cW * (uW + aW) + t * (vW + aW) - aW * (cW + t)` THEN
  SUBGOAL_THEN
   `cW * ((--sA * cW - cA * t) * (uW + aW) + (--sA * t + cA * cW) * vW) +
    (sA * cW + cA * t) * (cW * (uW + aW) + t * (vW + aW) - aW * (cW + t)) =
    cA * (vW + aW) - aW * (cA + sA * cW pow 2 + cA * cW * t)` ASSUME_TAC THENL
  [UNDISCH_TAC `cW pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCT_PROD_TAC `cA:real` `(&457 / &500) * t + &3 * cW - (vW + aW)` THEN
  PCT_PRODLT_TAC `aW - &1` `cA + sA * cW pow 2 + cA * cW * t` THEN
  UNDISCH_TAC `linside cA sA uA vA aA (&1) (&2)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  PCT_PRODLT_TAC `cW:real` `(vA + aA) - (--sA * &1 + cA * &2)` THEN
  RASM_ARITH_TAC);;

(* Lean: wall_axis *)
let CLWN_WALL_AXIS = prove
 (`forall cA sA uA vA aA cW sW uW vW aW t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cA sA /\ c977cc_normal cW t /\ sW = --t /\
     aA = aW /\ &1 < aW /\ aA <= &1001 / &1000 /\
     linside cA sA uA vA aA (&1) (&2) /\ linside cA sA uA vA aA (&2) (&3 / &2) /\
     lcont cW sW uW vW aW /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     ~linside cW sW uW vW aW (&457 / &500) (&3) /\
     ~linside cW sW uW vW aW (&19 / &25) (&187 / &100) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> uW + aW <= ABT_lower cA sA uA vA aA cW sW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --t`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    CLWN_NOT_CENTRAL_AXIS) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`]
    CLWS_NEGATIVE_ALTERNATIVES) THEN
  PCT_NORMAL_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MESON_TAC[]);;
