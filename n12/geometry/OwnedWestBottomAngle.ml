(* ========================================================================= *)
(* Port of Compact/Geometry/OwnedWestBottomAngle.lean (Jatloe, N12-jatloe).   *)
(* The owned-west central square rules out the steep negative bottom-marker  *)
(* escape; the remaining marker face forces a shallow bottom angle t < 1/5.  *)
(* Normal: c977cc_normal; boundary: c977cc_boundary; lower/upper: ABT_*;     *)
(* corner_face: C977NCO_CORNER_FACE; PositiveCentralLeftBand: PCLB_*;        *)
(* PositiveCentralTransverse.alternatives: PCT_ALTERNATIVES.                 *)
(* A square O with O.s = -t is cO sO uO vO aO with sO = --t.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/PositiveCentralLeftBand.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

let OWBA_PROD = PCT_PROD_TAC;;
let OWBA_PRODLT = PCT_PRODLT_TAC;;

let OWBA_BOUNDARY_EXACT = prove
 (`forall c t. &0 < c ==> c * c977cc_boundary c t = c + c * t + t - t pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c977cc_boundary] THEN
  UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;

(* Lean: upper_v_spread *)
let OWBA_UPPER_V_SPREAD = prove
 (`forall c t. c977cc_normal c t /\ c977cc_boundary c t < &2 * t + (&457 / &500) * c
         ==> &47 / &100 < t /\ &27 / &20 < c + t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] OWBA_BOUNDARY_EXACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c * c977cc_boundary c t < c * (&2 * t + (&457 / &500) * c)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c - &457 / &500 + t * (&1 - c) - (&43 / &500) * t pow 2 < &0`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&47 / &100 < t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   OWBA_PROD `&47 / &100 - t` `&47 / &100 + t` THEN
   SUBGOAL_THEN `&22 / &25 <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OWBA_PROD `&22 / &25 - c` `&22 / &25 + c` THEN RASM_ARITH_TAC; ALL_TAC] THEN
   OWBA_PROD `&1 - c` `c - &22 / &25` THEN
   SUBGOAL_THEN `&1 - c <= (&25 / &47) * t pow 2` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`t:real`; `(&1 - c) pow 2`] REAL_LE_MUL) THEN
   ASM_REWRITE_TAC[REAL_LE_POW_2] THEN DISCH_TAC THEN
   SUBGOAL_THEN `t * (&1 - c) - t pow 3 / &2 = t * (&1 - c) pow 2 / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `t pow 3 / &2 <= t * (&1 - c)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   OWBA_PROD `t:real` `&47 / &100 - t` THEN
   OWBA_PROD `&14521 / &23500 - &47 / &100` `&47 / &100 + t` THEN
   OWBA_PROD `&47 / &100` `&47 / &100 + t` THEN
   SUBGOAL_THEN `&0 <= &14521 / &23500 * (&47 / &100 + t) -
                       ((&47 / &100) pow 2 + &47 / &100 * t + t pow 2) / &2`
   ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   OWBA_PROD `&47 / &100 - t`
     `&14521 / &23500 * (&47 / &100 + t) -
      ((&47 / &100) pow 2 + &47 / &100 * t + t pow 2) / &2` THEN
   SUBGOAL_THEN `&43 / &500 - &14521 / &23500 * t pow 2 + t pow 3 / &2 =
       &14141 / &10000000 + (&47 / &100 - t) *
       (&14521 / &23500 * (&47 / &100 + t) -
        ((&47 / &100) pow 2 + &47 / &100 * t + t pow 2) / &2)` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  OWBA_PROD `t - &47 / &100` `&27 / &40 - t` THEN
  OWBA_PROD `&27 / &20 - t - c` `&27 / &20 - t + c` THEN
  RASM_ARITH_TAC);;

(* Lean: central_bounds (private) *)
let OWBA_CENTRAL_BOUNDS = prove
 (`forall C S. c977cc_normal C S /\ &13 * S <= &7 * C ==> &43 / &50 <= C /\ S <= &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  OWBA_PROD `&7 * C - &13 * S` `&7 * C + &13 * S` THEN
  SUBGOAL_THEN `S <= &1 / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   OWBA_PROD `S - &1 / &2` `S + &1 / &2` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  OWBA_PROD `&1 / &2 - S` `&1 / &2 + S` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  OWBA_PROD `&43 / &50 - C` `&43 / &50 + C` THEN RASM_ARITH_TAC);;

(* Lean: central_remainder (private) *)
let OWBA_CENTRAL_REMAINDER = prove
 (`forall c t C S. c977cc_normal c t /\ c977cc_normal C S /\ &43 / &50 <= C /\ S <= &1 / &2
     ==> (c + t) * ((&1 - C) - (&7 / &20) * S pow 2) -
         (c - t) * S * (&1 - (&7 / &20) * C) <= &19 / &280`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  OWBA_PROD `&1 - C` `(&27 / &50) * (&1 + C) - &1` THEN
  SUBGOAL_THEN `&1 - C <= (&27 / &50) * S pow 2` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  OWBA_PROD `c + t:real` `(&27 / &50) * S pow 2 - (&1 - C)` THEN
  OWBA_PROD `c - t:real` `S:real` THEN
  OWBA_PROD `(c - t) * S` `&1 - (&7 / &20) * C` THEN
  OWBA_PROD `&1 / &2 - S` `&1 / &2 + S` THEN
  OWBA_PROD `c + t:real` `&1 / &4 - S pow 2` THEN
  RASM_ARITH_TAC);;

(* Lean: own_axis_impossible *)
let OWBA_OWN_AXIS_IMPOSSIBLE = prove
 (`forall cO sO (uO:real) vO aO cA sA uA vA aA t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cO t /\ c977cc_normal cA sA /\
     &1 <= aA /\ &43 / &50 <= cA /\ sA <= &1 / &2 /\
     &47 / &100 < t /\ &27 / &20 < cO + t /\
     uA + aA <= &2 * (cA + sA) /\
     vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     c977cc_boundary cO t < vO + aO /\
     vO + aO <= ABT_lower cA sA uA vA aA t cO
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `t:real`; `cA:real`; `sA:real`] OWBA_CENTRAL_REMAINDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cO` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  OWBA_PROD `t:real` `cA:real` THEN OWBA_PROD `cO:real` `sA:real` THEN
  OWBA_PROD `cO:real` `cA - sA:real` THEN OWBA_PROD `sA:real` `cO - t:real` THEN
  SUBGOAL_THEN `&0 <= t * cA + cO * sA /\ &0 <= cO * cA - t * sA` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `t:real`; `cO:real`] PCT_LOWER_PP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  OWBA_PROD `t * cA + cO * sA` `&2 * (cA + sA) - (uA + aA)` THEN
  OWBA_PROD `cO * cA - t * sA` `((&47 / &20) * cA - (&33 / &20) * sA) - (vA + aA)` THEN
  OWBA_PROD `aA - &1` `(t * cA + cO * sA) + (cO * cA - t * sA)` THEN
  SUBGOAL_THEN
   `(t * cA + cO * sA) * (&2 * (cA + sA)) +
    (cO * cA - t * sA) * ((&47 / &20) * cA - (&33 / &20) * sA) -
    (t * cA + cO * sA) - (cO * cA - t * sA) =
    t + (&27 / &20) * cO + (cO + t) * ((&1 - cA) - (&7 / &20) * sA pow 2) -
    (cO - t) * sA * (&1 - (&7 / &20) * cA)` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(t * cA + cO * sA) * uA + (--t * sA + cO * cA) * vA <=
                t + (&27 / &20) * cO + &19 / &280`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `t:real`] OWBA_BOUNDARY_EXACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OWBA_PROD `t - &47 / &100` `t + &47 / &100` THEN
  SUBGOAL_THEN `&0 < cO * (c977cc_boundary cO t - (t + (&27 / &20) * cO + &19 / &280))`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `c977cc_boundary cO t - (t + (&27 / &20) * cO + &19 / &280)`]
    PCT_POS_BY_POS) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: central_axis_impossible *)
let OWBA_CENTRAL_AXIS_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cA sA (uA:real) vA aA t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cA sA /\
     aO = aA /\ &1 <= aO /\ &27 / &20 < cO + t /\
     t * (uO + aO) <= cO * vO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     ABT_upper cO sO uO vO aO (--sA) cA <= vA
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cO /\ &0 < cA` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  OWBA_PROD `cO:real` `cA - sA:real` THEN OWBA_PROD `sA:real` `cO - t:real` THEN
  OWBA_PROD `cO:real` `sA:real` THEN OWBA_PROD `t:real` `cA:real` THEN
  SUBGOAL_THEN `&0 <= cO * cA - t * sA /\ &0 <= cO * sA + t * cA` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aA:real`; `t:real`;
                `--sA`; `cA:real`] C977NCO_UPPER_NEGATIVE_NONPOS) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  UNDISCH_TAC `linside cO (--t) uO vO aA (&1) (&457 / &500)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `uO < cO - (&457 / &500) * t` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  OWBA_PROD `cO * cA - t * sA` `cO * vO - t * (uO + aA)` THEN
  OWBA_PROD `sA:real` `cO - (&457 / &500) * t - uO` THEN
  OWBA_PROD `cO * cA - t * sA` `cO + t:real` THEN
  OWBA_PROD `aA - &1` `(cO * cA - t * sA) * (cO + t) + cO` THEN
  OWBA_PROD `t:real` `&717 / &500 - (cO + t)` THEN
  SUBGOAL_THEN `&0 <= (&13 / &20) * cO - cO * t + (&457 / &500) * t - t pow 2`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  OWBA_PROD `sA:real` `(&13 / &20) * cO - cO * t + (&457 / &500) * t - t pow 2` THEN
  OWBA_PROD `cO:real` `&1 - cA` THEN
  OWBA_PRODLT `cO:real` `cA:real` THEN
  OWBA_PRODLT `cO * cA` `cO + t - &27 / &20` THEN
  SUBGOAL_THEN
   `cO * (((--sA * cO - cA * t) * uO + (--sA * t + cA * cO) * (vO + aA)) + aA -
          ((&47 / &20) * cA - (&33 / &20) * sA)) =
    (cO * cA - t * sA) * (cO * vO - t * (uO + aA)) +
    sA * (cO - (&457 / &500) * t - uO) +
    (aA - &1) * ((cO * cA - t * sA) * (cO + t) + cO) +
    cO * (&1 - cA) + (cO * cA) * (cO + t - &27 / &20) +
    sA * ((&13 / &20) * cO - cO * t + (&457 / &500) * t - t pow 2)` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`;
    `((--sA * cO - cA * t) * uO + (--sA * t + cA * cO) * (vO + aA)) + aA -
     ((&47 / &20) * cA - (&33 / &20) * sA)`] PCT_POS_BY_POS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: small_bottom *)
let OWBA_SMALL_BOTTOM = prove
 (`forall cO sO uO vO aO cA sA uA vA aA t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cA sA /\
     aO = aA /\ &1 < aA /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&1) (&2) /\
     uA + aA <= &2 * (cA + sA) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     ldisj cO sO uO vO aO cA sA uA vA aA
     ==> t < &1 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aA:real`; `t:real`]
    C977NCO_CORNER_FACE) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    PCLB_NORTHWEST_CAP) THEN
  PCT_NORMAL_TAC THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    PCLB_LEFT_POINT_TILT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] OWBA_CENTRAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < cO` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `uO + aA <= &2 * cO - (&457 / &500) * t \/
                vO + aA <= &2 * t + (&457 / &500) * cO` MP_TAC THENL
  [UNDISCH_TAC `~linside cO (--t) uO vO aA (&2) (&457 / &500)` THEN
   UNDISCH_TAC `linside cO (--t) uO vO aA (&1) (&457 / &500)` THEN
   REWRITE_TAC[linside] THEN STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
  [SUBGOAL_THEN `&1 - cO < (&43 / &500) * t` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   OWBA_PRODLT `&1 + cO` `(&43 / &500) * t - (&1 - cO)` THEN
   OWBA_PROD `t:real` `&1 - cO` THEN
   SUBGOAL_THEN `t pow 2 < (&43 / &250) * t` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`t:real`; `&43 / &250 - t`] PCT_POS_BY_POS) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; RASM_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `t:real`] OWBA_UPPER_V_SPREAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aA:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    PCT_ALTERNATIVES) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN STRIP_TAC THENL
  [MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aA:real`;
                 `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `t:real`] OWBA_OWN_AXIS_IMPOSSIBLE) THEN
   REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
   REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
   MP_TAC(SPECL [`cO:real`; `--t`; `uO:real`; `vO:real`; `aA:real`;
                 `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `t:real`] OWBA_CENTRAL_AXIS_IMPOSSIBLE) THEN
   REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
   REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC)]);;
