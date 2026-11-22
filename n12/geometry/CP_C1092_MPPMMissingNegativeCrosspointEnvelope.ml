(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointEnvelope.lean*)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointSupport).                   *)
(* MISSING-NEGATIVE-WALL-SCALARS section 2: both envelope bounds of FE.      *)
(* FE / E0 are c1092mmncs_FE / c1092mmncs_E0; kE / deltaE are c1092mncs_kE / *)
(* c1092mncs_deltaE; Quarter is c1092mncs_quarter; UnitCircleChord.increasing*)
(* is CCUCC_INCREASING; cosine_order is C977CSB_COSINE_ORDER.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointCentral.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointClamp.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092MMNCE_LIN = NLIN_TAC ~deg2:false [];;

let C1092MMNCE_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MMNCE_LIN; ALL_TAC];;

let C1092MMNCE_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092MMNCE_LIN; ALL_TAC];;

let C1092MMNCE_NORMAL_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)));;

(* Lean: leftSupport, rightSupport (private definitions) *)
let c1092mmnce_leftSupport = new_definition
 `c1092mmnce_leftSupport (d:real) t h r =
    --c1092mncs_deltaE d t h r * (d + t - &1) + c1092mncs_kE d t h r * c1092mmncs_E0 d t`;;
let c1092mmnce_rightSupport = new_definition
 `c1092mmnce_rightSupport (d:real) t h r =
    --c1092mncs_deltaE d t h r * (&1 + (&13 / &50) * t) + c1092mncs_kE d t h r * c1092mmncs_E0 d t`;;

(* Lean: FE_both_caps *)
let C1092MMNCE_FE_BOTH_CAPS = prove
 (`forall d t h r. c977cc_normal d t
     ==> c1092mmncs_FE d t h r <= c1092mmnce_leftSupport d t h r /\
         c1092mmncs_FE d t h r <= c1092mmnce_rightSupport d t h r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MMNCE_NORMAL_TAC THEN
  REWRITE_TAC[c1092mmncs_FE; c1092mmnce_leftSupport; c1092mmnce_rightSupport] THEN
  SPEC_TAC(`c1092mncs_deltaE d t h r`,`de:real`) THEN GEN_TAC THEN
  COND_CASES_TAC THENL
   [C1092MMNCE_PROD `&0 <= de * (&2 - d - (&37 / &50) * t)`;
    C1092MMNCE_PROD `&0 <= --de * (&2 - d - (&37 / &50) * t)`] THEN
  CONJ_TAC THEN C1092MMNCE_LIN);;

(* Lean: large_sum *)
let C1092MMNCE_LARGE_SUM = prove
 (`forall d t. c977cc_normal d t /\ &252 / &373 <= t ==> &141 / &100 <= d + t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MMNCE_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&275 / &373`; `&252 / &373`; `&1`; `&1`] CCUCC_INCREASING) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    REPEAT CONJ_TAC THEN C1092MMNCE_LIN;
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN C1092MMNCE_LIN]);;

(* Lean: FE_first_cap *)
let C1092MMNCE_FE_FIRST_CAP = prove
 (`forall d t h r. c977cc_normal d t /\ &252 / &373 <= t /\ c1092mncs_quarter h r
     ==> c1092mmncs_FE d t h r <= --(&19 / &100) * h - (&39 / &50) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MMNCE_LARGE_SUM) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MMNCE_FE_BOTH_CAPS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  C1092MMNCE_NORMAL_TAC THEN
  MP_TAC(SPEC `d - t:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  C1092MMNCE_FACT `d * t <= &1 / &2` THEN
  C1092MMNCE_FACT `&1 - d - t + (&11 / &25) * d * t <= --(&19 / &100)` THEN
  C1092MMNCE_PROD `&0 <= (d - t) * (&1 - (&11 / &50) * (d + t))` THEN
  C1092MMNCE_FACT `t - d - &14 / &25 - (&11 / &25) * t * t <= --(&39 / &50)` THEN
  C1092MMNCE_PROD `&0 <= (--(&19 / &100) - (&1 - d - t + (&11 / &25) * d * t)) * h` THEN
  C1092MMNCE_PROD `&0 <= (--(&39 / &50) - (t - d - &14 / &25 - (&11 / &25) * t * t)) * r` THEN
  SUBGOAL_THEN `c1092mmnce_leftSupport d t h r =
                (&1 - d - t + (&11 / &25) * d * t) * h +
                (t - d - &14 / &25 - (&11 / &25) * t * t) * r` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mmnce_leftSupport; c1092mncs_deltaE; c1092mncs_kE; c1092mmncs_E0] THEN
    UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MMNCE_LIN);;

(* Lean: FE_second_cap *)
let C1092MMNCE_FE_SECOND_CAP = prove
 (`forall d t h r. c977cc_normal d t /\ &252 / &373 <= t /\ c1092mncs_quarter h r
     ==> c1092mmncs_FE d t h r <= (&37 / &100) * h - (&33 / &25) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MMNCE_LARGE_SUM) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MMNCE_FE_BOTH_CAPS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&275 / &373`; `&252 / &373`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  SUBGOAL_THEN `c977cc_normal d t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal]; ALL_TAC] THEN
  C1092MMNCE_NORMAL_TAC THEN
  C1092MMNCE_PROD `&0 <= (&23 / &373 - (d - t)) * (&59 / &200 + (&3 / &20) * (&23 / &373 + d - t))` THEN
  C1092MMNCE_PROD `&0 <= (d - t) * (d + t - &141 / &100)` THEN
  C1092MMNCE_FACT `d - t + t * t - (&3 / &10) * d * t <= &37 / &100` THEN
  C1092MMNCE_PROD `&0 <= (d - t) * (d + t)` THEN
  MP_TAC(SPEC `d - t:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  C1092MMNCE_FACT `--d - t - &14 / &25 + (&3 / &10) * t * t + d * t <= --(&33 / &25)` THEN
  C1092MMNCE_PROD `&0 <= (&37 / &100 - (d - t + t * t - (&3 / &10) * d * t)) * h` THEN
  C1092MMNCE_PROD `&0 <= (--(&33 / &25) - (--d - t - &14 / &25 + (&3 / &10) * t * t + d * t)) * r` THEN
  SUBGOAL_THEN `c1092mmnce_rightSupport d t h r =
                (d - t + t * t - (&3 / &10) * d * t) * h +
                (--d - t - &14 / &25 + (&3 / &10) * t * t + d * t) * r` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mmnce_rightSupport; c1092mncs_deltaE; c1092mncs_kE; c1092mmncs_E0] THEN
    UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MMNCE_LIN);;
