(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalMargins.lean              *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  Full continuous successor   *)
(* margins from the exact rational endpoints and chord monotonicity.         *)
(* Normal: c977cc_normal; half: C1092WPS_half; FC/FE/P/Q: c1092mifss_*;      *)
(* CanonicalProjection.before: CCCP_BEFORE.                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalEndpoints.ml";;

let C1092MIFMG_LIN_TAC =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

(* add the unfolded form of every Normal assumption *)
let C1092MIFMG_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

(* th' an implication instance; its conclusion is added as an assumption *)
let C1092MIFMG_USE_TAC th' =
  SUBGOAL_THEN (rand(concl th')) ASSUME_TAC THENL
   [MATCH_MP_TAC th' THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     (REWRITE_TAC[c977cc_normal; c1092mifss_P; c1092mifss_Q] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN C1092MIFMG_LIN_TAC));
    ALL_TAC];;

let C1092MIFMG_NUM_TAC t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[c1092mifss_P; c1092mifss_Q; c977cc_normal; C1092WPS_half] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC];;

(* Lean: first_normal (private) *)
let C1092MIFMG_FIRST_NORMAL = prove
 (`c977cc_normal (&95727000 / &103958161) (&40541839 / &103958161)`,
  REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: last_normal (private) *)
let C1092MIFMG_LAST_NORMAL = prove
 (`c977cc_normal (&4165 / &4813) (&2412 / &4813)`,
  REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let C1092MIFMG_TENTH_NORMAL = prove
 (`c977cc_normal (&99 / &101) (&20 / &101) /\
   C1092WPS_half (&99 / &101) (&20 / &101) = &1 / &10`,
  REWRITE_TAC[c977cc_normal; C1092WPS_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: small_tenth *)
let C1092MIFMG_SMALL_TENTH = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &1 / &10
         ==> &49 / &50 < c /\ s < &1 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC C1092MIFMG_TENTH_NORMAL THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&99 / &101`; `&20 / &101`] C1092MIFE_HALF_CROSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&99 / &101`; `&20 / &101`; `c:real`; `s:real`]
    C1092MIFSS_COORDINATES_AFTER) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: centered_half_margins *)
let C1092MIFMG_CENTERED_HALF_MARGINS = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
     &49 / &50 < c /\ s < &9 / &50 /\ C1092WPS_half c s <= &91 / &1000 /\
     &0 <= c / &11 - s / &2 /\
     (&40541839 / &103958161) * d <= (&95727000 / &103958161) * t
     ==> &0 < c1092mifss_FC (&1 / &2) c s d t /\
         &0 < c1092mifss_FE (&1 / &2) (c / &11 - s / &2) c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC C1092MIFMG_FIRST_NORMAL THEN C1092MIFMG_UNFOLD_TAC THEN
  C1092MIFMG_USE_TAC(SPECL [`&1 / &2`; `d:real`; `t:real`;
    `&95727000 / &103958161`; `&40541839 / &103958161`] C1092MIFSS_COEFFICIENTS_AFTER) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  C1092MIFMG_NUM_TAC `c1092mifss_P (&95727000 / &103958161) (&40541839 / &103958161) < &9 / &10` THEN
  C1092MIFMG_NUM_TAC `c1092mifss_Q (&1 / &2) (&95727000 / &103958161) (&40541839 / &103958161) < &11 / &20` THEN
  MP_TAC(SPECL [`c:real`; `c1092mifss_P d t`; `&9 / &10`] REAL_LT_LMUL) THEN
  ANTS_TAC THENL [C1092MIFMG_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`s:real`; `c1092mifss_Q (&1 / &2) d t`; `&11 / &20`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [C1092MIFMG_LIN_TAC; DISCH_TAC] THEN
  C1092MIFMG_USE_TAC(SPECL [`&1 / &2`; `c / &11 - s / &2`; `c:real`; `s:real`; `d:real`; `t:real`;
    `&95727000 / &103958161`; `&40541839 / &103958161`] C1092MIFSS_FE_AFTER) THEN
  C1092MIFMG_USE_TAC(SPECL [`c:real`; `s:real`] C1092MIFE_CENTERED_HALF_ENDPOINT) THEN
  ASM_SIMP_TAC[C1092MIFSS_FC_FORMULA] THEN C1092MIFMG_LIN_TAC);;

(* Lean: centered_final_margins *)
let C1092MIFMG_CENTERED_FINAL_MARGINS = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
     &49 / &50 < c /\ s < &9 / &50 /\ C1092WPS_half c s <= &91 / &1000 /\
     &0 <= c / &11 - s / &2 /\
     (&2412 / &4813) * d <= (&4165 / &4813) * t
     ==> &0 < c1092mifss_FC (&13 / &50) c s d t /\
         &0 < c1092mifss_FE (&13 / &50) (c / &11 - s / &2) c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC C1092MIFMG_LAST_NORMAL THEN C1092MIFMG_UNFOLD_TAC THEN
  C1092MIFMG_USE_TAC(SPECL [`&13 / &50`; `d:real`; `t:real`;
    `&4165 / &4813`; `&2412 / &4813`] C1092MIFSS_COEFFICIENTS_AFTER) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  C1092MIFMG_NUM_TAC `c1092mifss_P (&4165 / &4813) (&2412 / &4813) < &177 / &200` THEN
  C1092MIFMG_NUM_TAC `c1092mifss_Q (&13 / &50) (&4165 / &4813) (&2412 / &4813) < &17 / &25` THEN
  MP_TAC(SPECL [`c:real`; `c1092mifss_P d t`; `&177 / &200`] REAL_LT_LMUL) THEN
  ANTS_TAC THENL [C1092MIFMG_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`s:real`; `c1092mifss_Q (&13 / &50) d t`; `&17 / &25`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [C1092MIFMG_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `c <= &1 - s * s / &2` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `&1 - c`]; ALL_TAC] THEN
  MP_TAC(SPECL [`&9 / &50 - s`; `&17 / &25 - (&177 / &400) * (s + &9 / &50)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [C1092MIFMG_LIN_TAC; DISCH_TAC] THEN
  C1092MIFMG_USE_TAC(SPECL [`&13 / &50`; `c / &11 - s / &2`; `c:real`; `s:real`; `d:real`; `t:real`;
    `&4165 / &4813`; `&2412 / &4813`] C1092MIFSS_FE_AFTER) THEN
  C1092MIFMG_USE_TAC(SPECL [`c:real`; `s:real`] C1092MIFE_CENTERED_FINAL_ENDPOINT) THEN
  ASM_SIMP_TAC[C1092MIFSS_FC_FORMULA] THEN C1092MIFMG_LIN_TAC);;

(* Lean: missing_final_margins *)
let C1092MIFMG_MISSING_FINAL_MARGINS = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ C1092WPS_half c s <= &1 / &10 /\
     (&2412 / &4813) * d <= (&4165 / &4813) * t
     ==> &0 < c1092mifss_FC (&13 / &50) c s d t /\
         &0 < c1092mifss_FE (&13 / &50) (&0) c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MIFMG_USE_TAC(SPECL [`c:real`; `s:real`] C1092MIFMG_SMALL_TENTH) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC C1092MIFMG_TENTH_NORMAL THEN STRIP_TAC THEN
  ASSUME_TAC C1092MIFMG_LAST_NORMAL THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&99 / &101`; `&20 / &101`] C1092MIFE_HALF_CROSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MIFMG_UNFOLD_TAC THEN
  C1092MIFMG_USE_TAC(SPECL [`c:real`; `s:real`; `&99 / &101`; `&20 / &101`;
    `c1092mifss_P (&4165 / &4813) (&2412 / &4813)`;
    `c1092mifss_Q (&13 / &50) (&4165 / &4813) (&2412 / &4813)`] CCCP_BEFORE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mifss_P; c1092mifss_Q]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  C1092MIFMG_USE_TAC(SPECL [`&13 / &50`; `c:real`; `s:real`; `d:real`; `t:real`;
    `&4165 / &4813`; `&2412 / &4813`] C1092MIFSS_FC_AFTER) THEN
  C1092MIFMG_USE_TAC(SPECL [`&13 / &50`; `&0`; `c:real`; `s:real`; `d:real`; `t:real`;
    `&4165 / &4813`; `&2412 / &4813`] C1092MIFSS_FE_AFTER) THEN
  C1092MIFMG_USE_TAC(SPECL [`c:real`; `s:real`] C1092MIFE_MISSING_FINAL_ENDPOINT) THEN
  SUBGOAL_THEN `&0 < c1092mifss_FC (&13 / &50) c s (&4165 / &4813) (&2412 / &4813)`
    ASSUME_TAC THENL
   [SIMP_TAC[C1092MIFSS_FC_FORMULA; REAL_ARITH `(&4165 / &4813) pow 2 + (&2412 / &4813) pow 2 = &1`] THEN
    REWRITE_TAC[c1092mifss_P; c1092mifss_Q] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN C1092MIFMG_LIN_TAC;
    ALL_TAC] THEN
  C1092MIFMG_LIN_TAC);;
