(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMElbowIsolationScalars.lean            *)
(* (N12Compact.C1092MPPMElbowScalars).  Exact simplifications of            *)
(* NONORDINARY-ISOLATION (9), (11), (13), (15).  Normal: c977cc_normal;      *)
(* relative_bounds: C1092UTS_RELATIVE_BOUNDS.                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_UpperThirdScalars.ml";;

let C1092EIS_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092EIS_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092EIS_LIN_TAC; DISCH_TAC];;

let C1092EIS_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

(* Lean: kappa *)
let c1092eis_kappa = new_definition `c1092eis_kappa (c:real) s d t = c * d + s * t`;;

(* Lean: sigma *)
let c1092eis_sigma = new_definition `c1092eis_sigma (c:real) s d t = c * t - s * d`;;

(* Lean: frames *)
let C1092EIS_FRAMES = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &7 / &10 < c1092eis_kappa c s d t /\ c1092eis_kappa c s d t <= &1 /\
         &0 <= c1092eis_kappa c s d t + c1092eis_sigma c s d t /\
         &0 <= c1092eis_kappa c s d t - c1092eis_sigma c s d t /\
         c1092eis_kappa c s d t * t - c1092eis_sigma c s d t * d = s /\
         c1092eis_kappa c s d t * s + c1092eis_sigma c s d t * c = t /\
         c1092eis_kappa c s d t * c - c1092eis_sigma c s d t * s = d /\
         c1092eis_sigma c s d t <= t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092UTS_RELATIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092EIS_NORMAL_TAC THEN REWRITE_TAC[c1092eis_kappa; c1092eis_sigma] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `(c * d + s * t) * t - (c * t - s * d) * d = s /\
                (c * d + s * t) * s + (c * t - s * d) * c = t /\
                (c * d + s * t) * c - (c * t - s * d) * s = d` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `d * d + t * t = &1` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092EIS_LE_MUL_TAC `d:real` `c - s` THEN C1092EIS_LE_MUL_TAC `t:real` `c + s` THEN
  C1092EIS_LE_MUL_TAC `d - t` `c:real` THEN C1092EIS_LE_MUL_TAC `s:real` `d + t` THEN
  C1092EIS_LE_MUL_TAC `&1 - c` `t:real` THEN C1092EIS_LE_MUL_TAC `s:real` `d:real` THEN
  REPEAT CONJ_TAC THEN C1092EIS_LIN_TAC);;

(* Lean: F0 *)
let c1092eis_F0 = new_definition
 `c1092eis_F0 c s d t =
    &1 - c - (&2 / &5) * s + (c1092eis_kappa c s d t + c1092eis_sigma c s d t) * (&1 - d) +
    (&2 / &5) * (c1092eis_kappa c s d t - c1092eis_sigma c s d t) * t`;;

(* Lean: F1 *)
let c1092eis_F1 = new_definition
 `c1092eis_F1 c s d t =
    &1 + c1092eis_kappa c s d t + c1092eis_sigma c s d t - d + (&2 / &5) * t -
    (c1092eis_kappa c s d t + c1092eis_sigma c s d t) * c -
    (&2 / &5) * (c1092eis_kappa c s d t - c1092eis_sigma c s d t) * s`;;

(* Lean: F2 *)
let c1092eis_F2 = new_definition
 `c1092eis_F2 c s d t =
    &1 - c - (&2 / &5) * s + c1092eis_kappa c s d t * (&1 - d + (&2 / &5) * t) -
    c1092eis_sigma c s d t * (&1 + (&13 / &50) * t)`;;

(* Lean: F3 *)
let c1092eis_F3 = new_definition
 `c1092eis_F3 c s d t =
    &1 + c1092eis_kappa c s d t - c1092eis_sigma c s d t - d + (&2 / &5) * t -
    c1092eis_kappa c s d t * c - (&2 / &5) * c1092eis_kappa c s d t * s +
    (&7 / &20) * c1092eis_sigma c s d t * (c + s)`;;

(* Lean: first_nonnegative *)
let C1092EIS_FIRST_NONNEGATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 <= c1092eis_sigma c s d t
     ==> &0 <= c1092eis_F0 c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092EIS_FRAMES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092EIS_NORMAL_TAC THEN
  REWRITE_TAC[c1092eis_F0] THEN
  C1092EIS_LE_MUL_TAC `c1092eis_kappa c s d t + c1092eis_sigma c s d t` `&1 - d` THEN
  C1092EIS_LE_MUL_TAC `c1092eis_sigma c s d t` `d - t` THEN
  C1092EIS_LIN_TAC);;

(* Lean: second_nonnegative *)
let C1092EIS_SECOND_NONNEGATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 <= c1092eis_sigma c s d t
     ==> &0 <= c1092eis_F1 c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092EIS_FRAMES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092EIS_NORMAL_TAC THEN
  REWRITE_TAC[c1092eis_F1] THEN
  C1092EIS_LE_MUL_TAC `c1092eis_kappa c s d t + c1092eis_sigma c s d t` `&1 - c` THEN
  C1092EIS_LE_MUL_TAC `c1092eis_sigma c s d t` `c + s` THEN
  C1092EIS_LIN_TAC);;

(* Lean: third_nonnegative *)
let C1092EIS_THIRD_NONNEGATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ c1092eis_sigma c s d t <= &0
     ==> &0 <= c1092eis_F2 c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092EIS_FRAMES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092EIS_NORMAL_TAC THEN
  REWRITE_TAC[c1092eis_F2] THEN
  C1092EIS_LE_MUL_TAC `c1092eis_kappa c s d t` `&1 - d` THEN
  C1092EIS_LE_MUL_TAC `--c1092eis_sigma c s d t` `&1 - (&2 / &5) * d + (&13 / &50) * t` THEN
  C1092EIS_LIN_TAC);;

(* Lean: fourth_nonnegative *)
let C1092EIS_FOURTH_NONNEGATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= &7 / &25 /\
             c1092eis_sigma c s d t <= &0
     ==> &0 <= c1092eis_F3 c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092EIS_FRAMES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092EIS_NORMAL_TAC THEN
  REWRITE_TAC[c1092eis_F3] THEN
  C1092EIS_LE_MUL_TAC `c1092eis_kappa c s d t` `&1 - c` THEN
  C1092EIS_LE_MUL_TAC `--c1092eis_sigma c s d t` `&1 - (&3 / &4) * c - (&7 / &20) * s` THEN
  C1092EIS_LIN_TAC);;
