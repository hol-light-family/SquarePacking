(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMElbowSuccessorScalars.lean           *)
(* (N12Compact.C1092MPPMElbowSuccessorScalars).  Full-interval successor     *)
(* margins.  kappa / sigma / frames: c1092eis_kappa / c1092eis_sigma /       *)
(* C1092EIS_FRAMES; Normal: c977cc_normal.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMElbowIsolationScalars.ml";;

let C1092ESS_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092ESS_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092ESS_LIN_TAC; DISCH_TAC];;

let C1092ESS_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092ESS_LIN_TAC; DISCH_TAC];;

let C1092ESS_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

let C1092ESS_PREP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092EIS_FRAMES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092ESS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092eis_kappa; c1092eis_sigma]) THEN
  REWRITE_TAC[c1092eis_kappa; c1092eis_sigma];;

(* Lean: own_before *)
let C1092ESS_OWN_BEFORE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ c1092eis_sigma c s d t <= &0
     ==> &0 <= &1 + c1092eis_kappa c s d t - c - (&2 / &5) * s -
               c1092eis_kappa c s d t * d + (&2 / &5) * c1092eis_kappa c s d t * t -
               c1092eis_sigma c s d t * (d + (&2 / &5) * t)`,
  C1092ESS_PREP_TAC THEN
  C1092ESS_LE_MUL_TAC `c * d + s * t` `&1 - d` THEN
  C1092ESS_LE_MUL_TAC `--(c * t - s * d)` `(&3 / &5) * d + (&2 / &5) * t` THEN
  C1092ESS_LIN_TAC);;

(* Lean: own_after *)
let C1092ESS_OWN_AFTER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 <= c1092eis_sigma c s d t
     ==> &0 <= &1 - c - (&2 / &5) * s +
               c1092eis_kappa c s d t * (&1 - d + (&2 / &5) * t) -
               (&7 / &20) * c1092eis_sigma c s d t * (d + t)`,
  C1092ESS_PREP_TAC THEN
  C1092ESS_LE_MUL_TAC `(c * d + s * t) - &7 / &10` `&1 - d` THEN
  MP_TAC(SPEC `&1 - d` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  C1092ESS_LE_MUL_TAC `t - (c * t - s * d)` `t:real` THEN
  C1092ESS_LE_MUL_TAC `c * t - s * d` `d:real` THEN
  C1092ESS_LIN_TAC);;

(* Lean: transverse_before *)
let C1092ESS_TRANSVERSE_BEFORE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ c + s < &31 / &25 /\
             c1092eis_sigma c s d t <= &0
     ==> &0 < c1092eis_kappa c s d t * (&1 - (&7 / &10) * (c + s)) -
              c1092eis_sigma c s d t * (&1 + (&7 / &20) * c - (&9 / &100) * s)`,
  C1092ESS_PREP_TAC THEN
  C1092ESS_LT_MUL_TAC `c * d + s * t` `&1 - (&7 / &10) * (c + s)` THEN
  C1092ESS_LE_MUL_TAC `--(c * t - s * d)` `&1 + (&7 / &20) * c - (&9 / &100) * s` THEN
  C1092ESS_LIN_TAC);;

(* Lean: transverse_after_small *)
let C1092ESS_TRANSVERSE_AFTER_SMALL = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s < &7 / &25 /\
             c + s < &31 / &25 /\ &0 <= c1092eis_sigma c s d t /\
             &47 / &50 < d /\ t < &8 / &25
     ==> &0 < c1092eis_kappa c s d t * (&1 - (&7 / &10) * (c + s)) +
              c1092eis_sigma c s d t * (&1 - (&27 / &20) * c - (&1 / &20) * s)`,
  C1092ESS_PREP_TAC THEN
  C1092ESS_LE_MUL_TAC `c * d + s * t` `&1 - c` THEN
  C1092ESS_LE_MUL_TAC `c * t - s * d` `s:real` THEN
  SUBGOAL_THEN `&47 / &50 < c * d + s * t /\ c * t - s * d < &8 / &25` STRIP_ASSUME_TAC
  THENL [CONJ_TAC THEN C1092ESS_LIN_TAC; ALL_TAC] THEN
  C1092ESS_LE_MUL_TAC `c * d + s * t` `(&1 - (&7 / &10) * (c + s)) - &33 / &250` THEN
  C1092ESS_LE_MUL_TAC `c * t - s * d` `(&1 - (&27 / &20) * c - (&1 / &20) * s) + &91 / &250` THEN
  C1092ESS_LIN_TAC);;

(* Lean: transverse_corner *)
let C1092ESS_TRANSVERSE_CORNER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &24 / &25 < c /\ s < &7 / &25
     ==> &0 < &1 + c1092eis_kappa c s d t + c1092eis_sigma c s d t -
              (&27 / &20) * c1092eis_kappa c s d t * (c + s) -
              c1092eis_sigma c s d t * (&2 * c - (&3 / &5) * s)`,
  C1092ESS_PREP_TAC THEN
  ABBREV_TAC `A = (&27 / &20) * (c + s) - &1` THEN
  ABBREV_TAC `B = &2 * c - (&3 / &5) * s - &1` THEN
  SUBGOAL_THEN `&0 <= A /\ &0 <= B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092ESS_LIN_TAC; ALL_TAC] THEN
  C1092ESS_LE_MUL_TAC `A:real` `c + s` THEN C1092ESS_LE_MUL_TAC `B:real` `c - s` THEN
  ABBREV_TAC `TT = A * (c + s) + B * (c - s)` THEN
  ABBREV_TAC `D = B * (c + s) - A * (c - s)` THEN
  SUBGOAL_THEN `D = &13 / &20 + (&1 / &10) * s * s + (&7 / &5) * c * s - &2 * s /\
                TT - &27 / &20 = (&1 - c) * (&3 / &5 - (&7 / &5) * c) + (&1 / &10) * c * s /\
                &2 * (A * (c * d + s * t) + B * (c * t - s * d)) = TT * (d + t) - D * (d - t)`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "TT"; "A"; "B"] THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092ESS_LE_MUL_TAC `c:real` `s:real` THEN
  MP_TAC(SPEC `s:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL [C1092ESS_LIN_TAC; ALL_TAC] THEN
  C1092ESS_LE_MUL_TAC `&1 - c` `(&7 / &5) * c - &3 / &5` THEN
  C1092ESS_LE_MUL_TAC `&1 - c` `s:real` THEN
  SUBGOAL_THEN `&0 <= TT /\ TT < &7 / &5` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092ESS_LIN_TAC; ALL_TAC] THEN
  C1092ESS_LE_MUL_TAC `TT:real` `&10 / &7 - (d + t)` THEN
  C1092ESS_LE_MUL_TAC `D:real` `d - t` THEN
  SUBGOAL_THEN `A * (c * d + s * t) + B * (c * t - s * d) < &1` ASSUME_TAC THENL
   [C1092ESS_LIN_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REAL_ARITH_TAC);;

(* Lean: corner_angle *)
let C1092ESS_CORNER_ANGLE = prove
 (`forall d t. c977cc_normal d t /\ &130 * t < &43 * d ==> &47 / &50 < d /\ t < &8 / &25`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ESS_NORMAL_TAC THEN
  C1092ESS_LT_MUL_TAC `&43 * d - &130 * t` `&43 * d + &130 * t` THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
   [C1092ESS_LE_MUL_TAC `&47 / &50 - d` `&47 / &50 + d`;
    C1092ESS_LE_MUL_TAC `t - &8 / &25` `t + &8 / &25`] THEN
  C1092ESS_LIN_TAC);;

(* Lean: narrow_width *)
let C1092ESS_NARROW_WIDTH = prove
 (`forall d t. c977cc_normal d t /\ &1 < d + (&43 / &500) * t ==> &130 * t < &43 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ESS_NORMAL_TAC THEN
  C1092ESS_LT_MUL_TAC `d + (&43 / &500) * t - &1` `d + (&43 / &500) * t + &1` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092ESS_LE_MUL_TAC `t:real` `&130 * t - &43 * d` THEN
  MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  C1092ESS_LIN_TAC);;
