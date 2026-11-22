(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeWallAngleOrder.lean (Jatloe, N12-jatloe). *)
(* A negative left wall separating from the positive central square has      *)
(* strictly larger sine magnitude.  Normal: c977cc_normal; lower: ABT_lower; *)
(* W with W.s = -t is cW sW uW vW aW with sW = --t.                          *)
(* PositiveCentralLeftBand: PCLB_*; LeftWallNegativeFaces.faces: LWNF_FACES; *)
(* CentralLeftWallNegative.wall_axis: CLWN_WALL_AXIS.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralLeftWallNegative.ml";;
needs "n12/geometry/PositiveCentralLeftBand.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

let NWAO_PROD = PCT_PROD_TAC;;
let NWAO_PRODLT = PCT_PRODLT_TAC;;

(* Lean: central_bounds (private) *)
let NWAO_CENTRAL_BOUNDS = prove
 (`forall C S. c977cc_normal C S /\ &13 * S <= &7 * C ==> &7 / &8 <= C /\ S <= &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  NWAO_PROD `&7 * C - &13 * S` `&7 * C + &13 * S` THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
  [NWAO_PROD `&7 / &8 - C` `&7 / &8 + C` THEN RASM_ARITH_TAC;
   NWAO_PRODLT `S - &1 / &2` `S + &1 / &2` THEN RASM_ARITH_TAC]);;

(* Lean: ordered_normals (private) *)
let NWAO_ORDERED_NORMALS = prove
 (`forall C S d t. c977cc_normal C S /\ c977cc_normal d t /\ t <= S
             ==> C <= d /\ d * t <= C * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  NWAO_PROD `S - t:real` `S + t:real` THEN
  SUBGOAL_THEN `C <= d` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   NWAO_PRODLT `C - d:real` `C + d:real` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  NWAO_PROD `C - t:real` `C + t:real` THEN
  SUBGOAL_THEN `&0 <= &1 - S pow 2 - t pow 2 /\ &0 <= S pow 2 - t pow 2`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NWAO_PROD `S pow 2 - t pow 2` `&1 - S pow 2 - t pow 2` THEN
  SUBGOAL_THEN `(C * S) pow 2 - (d * t) pow 2 = (S pow 2 - t pow 2) * (&1 - S pow 2 - t pow 2)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  NWAO_PROD `C:real` `S:real` THEN NWAO_PROD `d:real` `t:real` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NWAO_PRODLT `d * t - C * S` `d * t + C * S` THEN RASM_ARITH_TAC);;

(* Lean: H (private definition) *)
let nwao_H = new_definition
 `nwao_H (d:real) (t:real) = (&1 - d) * (&1 - t) - (&43 / &500) * t pow 2`;;

(* Lean: h_order (private) *)
let NWAO_H_ORDER = prove
 (`forall C S d t. c977cc_normal C S /\ c977cc_normal d t /\ S <= &1 / &2 /\ t <= S
             ==> nwao_H d t <= nwao_H C S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&41 / &125 <= &1 - S - (&43 / &500) * (d + C)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  NWAO_PROD `S + t:real` `(&1 - S - (&43 / &500) * (d + C)) - &41 / &125` THEN
  NWAO_PROD `&1 - d` `&1 - C` THEN
  NWAO_PROD `t:real` `&1 / &2 - t` THEN
  SUBGOAL_THEN `&0 <= (S + t) * (&1 - S - (&43 / &500) * (d + C)) - (&1 - d) * (d + C)`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NWAO_PROD `S - t:real`
    `(S + t) * (&1 - S - (&43 / &500) * (d + C)) - (&1 - d) * (d + C)` THEN
  SUBGOAL_THEN
   `(d + C) * (nwao_H C S - nwao_H d t) =
    (S - t) * ((S + t) * (&1 - S - (&43 / &500) * (d + C)) - (&1 - d) * (d + C))`
  ASSUME_TAC THENL
  [REWRITE_TAC[nwao_H] THEN
   UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NWAO_PRODLT `d + C:real` `nwao_H d t - nwao_H C S` THEN RASM_ARITH_TAC);;

(* Lean: equal_order (private) *)
let NWAO_EQUAL_ORDER = prove
 (`forall C S. c977cc_normal C S /\ &7 / &8 <= C
         ==> &0 <= (&1 - C) * C * (C pow 2 - S pow 2) - nwao_H C S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= &1 - &2 * C * S` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `C - S:real`]; ALL_TAC] THEN
  NWAO_PROD `&1 - C` `S:real` THEN
  NWAO_PROD `(&1 - C) * S` `&1 - &2 * C * S` THEN
  NWAO_PROD `&1 - C` `(&543 / &500) * C - &457 / &500` THEN
  SUBGOAL_THEN
   `(&1 - C) * C * (C pow 2 - S pow 2) - nwao_H C S =
    (&1 - C) * S * (&1 - &2 * C * S) + (&1 - C) * ((&543 / &500) * C - &457 / &500)`
  SUBST1_TAC THENL
  [REWRITE_TAC[nwao_H] THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; RASM_ARITH_TAC]);;

(* Lean: scalar *)
let NWAO_SCALAR = prove
 (`forall C S d t. c977cc_normal C S /\ c977cc_normal d t /\ &13 * S <= &7 * C /\ t <= S
     ==> &0 <= (&1 - C) * d * (C * d - S * t) - (&1 - d) * (&1 - t) +
               (&43 / &500) * t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] NWAO_CENTRAL_BOUNDS) THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `d:real`; `t:real`] NWAO_ORDERED_NORMALS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `d:real`; `t:real`] NWAO_H_ORDER) THEN
  MP_TAC(SPECL [`C:real`; `S:real`] NWAO_EQUAL_ORDER) THEN
  ASM_REWRITE_TAC[nwao_H] THEN REPEAT DISCH_TAC THEN PCT_NORMAL_TAC THEN
  NWAO_PROD `d - C:real` `d + C:real` THEN
  NWAO_PROD `C:real` `(d - C) * (d + C)` THEN
  NWAO_PROD `S:real` `C * S - d * t` THEN
  SUBGOAL_THEN `C * (C pow 2 - S pow 2) <= d * (C * d - S * t)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  NWAO_PROD `&1 - C` `d * (C * d - S * t) - C * (C pow 2 - S pow 2)` THEN
  RASM_ARITH_TAC);;

(* Lean: support_order *)
let NWAO_SUPPORT_ORDER = prove
 (`forall cA sA uA vA aA cW sW uW vW aW t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cA sA /\ c977cc_normal cW t /\ sW = --t /\
     aA = aW /\ &1 < aA /\ &13 * sA <= &7 * cA /\
     uA + aA <= &2 * (cA + sA) /\ linside cA sA uA vA aA (&1) (&2) /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     aW * (cW + t) <= cW * (uW + aW) + t * (vW + aW) /\
     uW + aW <= ABT_lower cA sA uA vA aA cW sW
     ==> sA < t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aW`)) THEN
  PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cA /\ &0 < cW` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NWAO_PROD `cW:real` `cA - sA:real` THEN NWAO_PROD `sA:real` `cW - t:real` THEN
  NWAO_PROD `sA:real` `cW:real` THEN NWAO_PROD `cA:real` `t:real` THEN
  SUBGOAL_THEN `&0 <= cA * cW - sA * t /\ &0 <= sA * cW + cA * t` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aW:real`;
                `cW:real`; `--t`] PCT_LOWER_PN) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  UNDISCH_TAC `linside cA sA uA vA aW (&1) (&2)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NWAO_PROD `cA * cW - sA * t` `&2 * (cA + sA) - (uA + aW)` THEN
  NWAO_PROD `sA * cW + cA * t` `(vA + aW) - (--sA * &1 + cA * &2)` THEN
  SUBGOAL_THEN `uW + aW <= (cA * cW - sA * t) * (&2 * (cA + sA) - aW) -
                (sA * cW + cA * t) * (&2 * cA - sA)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  NWAO_PROD `cW:real` `((cA * cW - sA * t) * (&2 * (cA + sA) - aW) -
                       (sA * cW + cA * t) * (&2 * cA - sA)) - (uW + aW)` THEN
  NWAO_PROD `t:real` `((&457 / &500) * t + &3 * cW) - (vW + aW)` THEN
  NWAO_PROD `cW:real` `cA * cW - sA * t` THEN
  SUBGOAL_THEN `&0 < cW + t + cW * (cA * cW - sA * t)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `aW * (cW + t + cW * (cA * cW - sA * t)) <=
    cW * (&2 * (cA * cW - sA * t) * (cA + sA) - (sA * cW + cA * t) * (&2 * cA - sA)) +
    (&457 / &500) * t pow 2 + &3 * cW * t` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  NWAO_PRODLT `aW - &1` `cW + t + cW * (cA * cW - sA * t)` THEN
  SUBGOAL_THEN
   `(&1 - cA) * cW * (cA * cW - sA * t) - (&1 - cW) * (&1 - t) + (&43 / &500) * t pow 2 =
    (cW + t + cW * (cA * cW - sA * t)) -
    (cW * (&2 * (cA * cW - sA * t) * (cA + sA) - (sA * cW + cA * t) * (&2 * cA - sA)) +
     (&457 / &500) * t pow 2 + &3 * cW * t)` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN UNDISCH_TAC `cW pow 2 + t pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `t:real`] NWAO_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN RASM_ARITH_TAC);;

(* Lean: angle_order *)
let NWAO_ANGLE_ORDER = prove
 (`forall cA sA uA vA aA cW sW uW vW aW t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cA sA /\ c977cc_normal cW t /\ sW = --t /\
     aA = aW /\ &1 < aA /\ aA <= &1001 / &1000 /\
     uA + aA <= &2 * (cA + sA) /\
     linside cA sA uA vA aA (&1) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     lcont cW sW uW vW aW /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     ~linside cW sW uW vW aW (&457 / &500) (&3) /\
     ~linside cW sW uW vW aW (&19 / &25) (&187 / &100) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> sA < t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aW`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aW:real`;
                `cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    CLWN_WALL_AXIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  PCT_NORMAL_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aW:real`]
    PCLB_NORTHWEST_CAP) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aW:real`]
    PCLB_LEFT_POINT_TILT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~linside cW (--t) uW vW aW (&1) (&2)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cA sA uA vA aW cW (--t) uW vW aW` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&1`; `&2`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    LWNF_FACES) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); STRIP_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aW:real`;
                `cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    NWAO_SUPPORT_ORDER) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC));;
