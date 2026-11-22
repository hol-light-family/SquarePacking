(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeBottomNextAxes.lean (Jatloe, N12-jatloe). *)
(* The missing-corner negative singleton O has two marker faces; with the    *)
(* next wall D only two upward axes remain.  Normal: c977cc_normal;          *)
(* boundary: c977cc_boundary; lower/upper: ABT_lower/ABT_upper; a square     *)
(* with q.s = -s is written with the hypothesis sO = --s.                    *)
(* C696BottomChainSelectors.singleton_wall: C696BCS_SINGLETON_WALL;          *)
(* NegativeBottomInnerWall.negative_projection: NBIW_NEGATIVE_PROJECTION;    *)
(* OwnedWestBottomAngle.upper_v_spread: OWBA_UPPER_V_SPREAD.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/NegativeBottomInnerWall.ml";;
needs "n12/geometry/C696BottomChainSelectors.ml";;
needs "n12/geometry/OwnedWestBottomAngle.ml";;

(* Lean: marker_escape *)
let NBNA_MARKER_ESCAPE = prove
 (`forall cO sO uO vO aO s.
     cO * cO + sO * sO = &1 /\ &0 < aO /\
     sO = --s /\ c977cc_normal cO s /\ &1 < aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     cO - s <= uO /\ c977cc_boundary cO s < vO + aO
     ==> s < &1 / &5 \/ (&47 / &100 < s /\ &27 / &20 < cO + s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --s`)) THEN
  PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cO` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `uO + aO <= &2 * cO - (&457 / &500) * s \/
                vO + aO <= &2 * s + (&457 / &500) * cO` MP_TAC THENL
  [UNDISCH_TAC `~linside cO (--s) uO vO aO (&2) (&457 / &500)` THEN
   UNDISCH_TAC `linside cO (--s) uO vO aO (&1) (&457 / &500)` THEN
   REWRITE_TAC[linside] THEN STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
  [DISJ1_TAC THEN
   SUBGOAL_THEN `&1 - cO < (&43 / &500) * s` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   PCT_PRODLT_TAC `&1 + cO` `(&43 / &500) * s - (&1 - cO)` THEN
   PCT_PROD_TAC `s:real` `&1 - cO` THEN
   SUBGOAL_THEN `s pow 2 < (&43 / &250) * s` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`s:real`; `&43 / &250 - s`] PCT_POS_BY_POS) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; RASM_ARITH_TAC];
   DISJ2_TAC THEN MATCH_MP_TAC OWBA_UPPER_V_SPREAD THEN
   ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]);;

(* Lean: negative_wall *)
let NBNA_NEGATIVE_WALL = prove
 (`forall cO sO uO vO aO cD sD uD vD aD s r.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     sO = --s /\ sD = --r /\ c977cc_normal cO s /\ c977cc_normal cD r /\
     aO = aD /\ &1 < aO /\
     cO - s <= uO /\ s * (uO + aO) <= cO * vO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&87 / &50) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&2) (&1) /\
     ldisj cO sO uO vO aO cD sD uD vD aD
     ==> vO + aO <= ABT_lower cD sD uD vD aD s cO \/
         ABT_upper cO sO uO vO aO r cD <= vD`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --s`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aD`)) THEN
  MP_TAC(SPECL [`cO:real`; `--s`; `uO:real`; `vO:real`; `aD:real`;
                `cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`]
    C696BCS_SINGLETON_WALL) THEN
  MP_TAC(SPECL [`cO:real`; `--s`; `uO:real`; `vO:real`; `aD:real`;
                `s:real`; `cO:real`; `s:real`] NBIW_NEGATIVE_PROJECTION) THEN
  MP_TAC(SPECL [`cO:real`; `--s`; `uO:real`; `vO:real`; `aD:real`;
                `s:real`; `cD:real`; `r:real`] NBIW_NEGATIVE_PROJECTION) THEN
  PCT_NORMAL_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
  REWRITE_TAC[C696BCS_singletonStep] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  ABT_SB_TAC [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`]
    `&2` `&1` `cO:real` `--s` THEN
  ABT_SB_TAC [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`]
    `&2` `&1` `cD:real` `--r` THEN
  MP_TAC(SPECL [`cO:real`; `--s`; `uO:real`; `vO:real`; `aD:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl))) THEN
  ABT_ARITH_TAC);;

(* Lean: positive_wall *)
let NBNA_POSITIVE_WALL = prove
 (`forall cO sO uO vO aO cD sD uD vD aD s.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     sO = --s /\ c977cc_normal cO s /\ c977cc_normal cD sD /\
     aO = aD /\ &1 < aO /\ &47 / &100 < s /\ cO - s <= uO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&87 / &50) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     ldisj cO sO uO vO aO cD sD uD vD aD
     ==> vO + aO <= ABT_lower cD sD uD vD aD s cO \/
         ABT_upper cO sO uO vO aO cD sD <= uD`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --s`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aD`)) THEN
  MP_TAC(SPECL [`cO:real`; `--s`; `uO:real`; `vO:real`; `aD:real`;
                `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`]
    C696BCS_SINGLETON_WALL) THEN
  PCT_NORMAL_TAC THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
  REWRITE_TAC[C696BCS_singletonStep] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  SUBGOAL_THEN `s <= &5 / &7` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PROD_TAC `s - &47 / &100` `s + &47 / &100` THEN
  SUBGOAL_THEN `cO <= &9 / &10` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCT_PROD_TAC `cO - &9 / &10` `cO + &9 / &10` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABT_SB_TAC [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`]
    `&2` `&457 / &500` `cO:real` `--s` THEN
  MP_TAC(SPECL [`cO:real`; `--s`; `uO:real`; `vO:real`; `aD:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cO:real`; `--s`; `uO:real`; `vO:real`; `aD:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl))) THEN
  ABT_ARITH_TAC);;
