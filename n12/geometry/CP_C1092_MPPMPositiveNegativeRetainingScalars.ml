(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveNegativeRetainingScalars.lean*)
(* (N12Compact.C1092MPPMPositiveNegativeRetaining.Scalars).  Exact scalar    *)
(* part of POSITIVE-NEGATIVE-RETAINING-SHALLOW.  Normal is c977cc_normal;    *)
(* norm_lt is C1092NPP_NORM_LT; canonical_bounds C1092PRS_CANONICAL_BOUNDS;  *)
(* SteepPositiveNegativeProfile envelope: C1092SNP_ENVELOPE.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveNegativeProfileScalars.ml";;

let C1092PNRS_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: P, Q (definitions) *)
let c1092pnrs_P = new_definition
 `c1092pnrs_P (d:real) (t:real) = &1 - t + (&13 / &50) * d * t + t pow 2 / &2`;;
let c1092pnrs_Q = new_definition
 `c1092pnrs_Q (d:real) (t:real) = &1 - d + d * t / &2 - (&13 / &50) * t pow 2`;;

(* Lean: first_margin *)
let C1092PNRS_FIRST_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 < t
     ==> &0 < &1 - c1092pnrs_P d t * c - c1092pnrs_Q d t * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c1092pnrs_P d t`; `c1092pnrs_Q d t`; `c:real`; `s:real`; `&1`]
    C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  REWRITE_TAC[c1092pnrs_P; c1092pnrs_Q] THEN
  ABBREV_TAC `P = &1 - t + (&13 / &50) * d * t + t pow 2 / &2` THEN
  ABBREV_TAC `Q = &1 - d + d * t / &2 - (&13 / &50) * t pow 2` THEN
  C1092PRS_PROD `&0 <= d * t` THEN C1092PRS_PROD `&0 <= t * t` THEN
  C1092PRS_PROD `&0 <= t * (d / &2 - (&13 / &50) * t)` THEN
  C1092PRS_PROD `&0 <= t * (&31 / &50 - (&13 / &50) * d - t / &2)` THEN
  C1092PRS_PROD `&0 <= t * ((&21 / &50) * (&1 + d) - t)` THEN
  C1092PRS_PROD `&0 <= t * (&1 - d)` THEN
  SUBGOAL_THEN `&0 <= P /\ &0 <= Q /\ P <= &1 - (&19 / &50) * t` STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN REWRITE_TAC[REAL_POW_2] THEN C1092PNRS_LP_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&1 - d <= (&21 / &50) * t` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1 + d) * ((&21 / &50) * t - (&1 - d))` MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092PNRS_LP_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 < (&1 + d) * ((&1 - d) - (&21 / &50) * t)` THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `Q <= (&23 / &25) * t` ASSUME_TAC THENL
  [EXPAND_TAC "Q" THEN REWRITE_TAC[REAL_POW_2] THEN C1092PNRS_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= ((&1 - (&19 / &50) * t) - P) * ((&1 - (&19 / &50) * t) + P)` THEN
  C1092PRS_PROD `&0 <= ((&23 / &25) * t - Q) * ((&23 / &25) * t + Q)` THEN
  C1092PRS_PROD `&0 < t * (&19 / &25 - (&2477 / &2500) * t)` THEN
  REWRITE_TAC[REAL_POW_2] THEN C1092PNRS_LP_TAC);;

(* Lean: transverse_margin *)
let C1092PNRS_TRANSVERSE_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 <= c * d - s * t /\
             c * t + s * d <= &1
     ==> &0 < &1 - s + (c * d - s * t) * (&1 - d) - (&13 / &50) * (c * t + s * d) * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= (c * d - s * t) * (&1 - d)` THEN
  C1092PRS_PROD `&0 <= (&1 - (c * t + s * d)) * t` THEN
  C1092PNRS_LP_TAC);;

(* Lean: envelope *)
let C1092PNRS_ENVELOPE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> d * (&1 + c * s - c - s) - t * (c - s + s pow 2) < (&43 / &500) * d - t / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SNP_ENVELOPE) THEN
  ASM_REWRITE_TAC[c1092snp_f; c1092snp_B] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 < d * (&43 / &500 - (&1 + c * s - c - s))` THEN
  C1092PRS_PROD `&0 <= t * ((c - s + s pow 2 - &13 / &50) - &6 / &25)` THEN
  C1092PNRS_LP_TAC);;

(* Lean: preliminary *)
let C1092PNRS_PRELIMINARY = prove
 (`forall d t H. c977cc_normal d t /\ --(&13 / &50) * t < H /\ H < (&43 / &500) * d - t / &2
           ==> t < (&2 / &5) * d /\ &23 / &25 < d /\ t < &19 / &50`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `t < (&2 / &5) * d` ASSUME_TAC THENL [C1092PNRS_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 < ((&2 / &5) * d - t) * ((&2 / &5) * d + t)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
  [C1092PRS_PROD `&0 <= (&23 / &25 - d) * (&23 / &25 + d)`;
   C1092PRS_PROD `&0 <= (t - &19 / &50) * (t + &19 / &50)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092PNRS_LP_TAC);;

(* Lean: sharpen *)
let C1092PNRS_SHARPEN = prove
 (`forall d t H. c977cc_normal d t /\ &0 < t /\ &23 / &25 < d /\ t < &19 / &50 /\
           H < (&43 / &500) * d - t / &2 /\ d + t - &1 - d * t < d * H
           ==> &4 * t < d /\ H < &43 / &500 /\ &97 / &100 < d /\ t < &1 / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&4 * t < d` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&23 / &100 < t` ASSUME_TAC THENL [C1092PNRS_LP_TAC; ALL_TAC] THEN
   C1092PRS_PROD `&0 <= (&1 - d) * ((&21 / &40) * (&1 + d) - &1)` THEN
   SUBGOAL_THEN `&1 - (&21 / &40) * t * t <= d` ASSUME_TAC THENL
   [C1092PNRS_LP_TAC; ALL_TAC] THEN
   C1092PRS_PROD `&0 <= (d - (&1 - (&21 / &40) * t * t)) * (&1 - t / &2)` THEN
   C1092PRS_PROD `&0 <= (t - &23 / &100) * (&1 / &2 - (&439 / &1000) * (t + &23 / &100))` THEN
   C1092PRS_PROD `&0 <= t * (t * t)` THEN
   SUBGOAL_THEN `&0 < d + t - &1 - d * t / &2 - (&43 / &500) * d * d` ASSUME_TAC THENL
   [C1092PNRS_LP_TAC; ALL_TAC] THEN
   C1092PRS_PROD `&0 < d * ((&43 / &500) * d - t / &2 - H)` THEN
   C1092PNRS_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `H < &43 / &500` ASSUME_TAC THENL [C1092PNRS_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 < (d - &4 * t) * (d + &4 * t)` THEN
  SUBGOAL_THEN `&97 / &100 < d` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 <= (&97 / &100 - d) * (&97 / &100 + d)` THEN C1092PNRS_LP_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C1092PNRS_LP_TAC);;
