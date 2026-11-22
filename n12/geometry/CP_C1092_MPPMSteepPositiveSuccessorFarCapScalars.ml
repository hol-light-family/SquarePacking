(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMSteepPositiveSuccessorFarCapScalars  *)
(* .lean (N12Compact.C1092MPPMSteepPositiveSuccessorFarCap.Scalars).         *)
(* Rational bounds for STEEP-POSITIVE-SUCCESSOR-FAR-CAP.  Normal is         *)
(* c977cc_normal; kappa/sigma etc. are c1092prs_*; cosine_cap is            *)
(* C1092UTS_COSINE_CAP.                                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;
needs "n12/geometry/CP_C1092_MMMP_UpperThirdScalars.ml";;

(* Lean: central_bounds *)
let C1092SFC_CENTRAL_BOUNDS = prove
 (`forall c s a U V. c977cc_normal c s /\ &3 / &5 <= s /\ &1 < a /\ --c - s <= U /\
               (&14 / &25) * s - c <= V /\ V + a <= (&543 / &500) * s
               ==> --(&83 / &200) < U + a /\ &67 / &125 < V + a /\ V + a < &96 / &125 /\
                   &29 / &125 < --V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092UTS_COSINE_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `c + s < &283 / &200` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 <= (c + s - &283 / &200) * (c + s + &283 / &200)` THEN
   NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (c - s) * (c + s)` THEN
  SUBGOAL_THEN `(&543 / &500) * s < &96 / &125` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 <= ((&543 / &500) * s - &96 / &125) * ((&543 / &500) * s + &96 / &125)` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: wall_width *)
let C1092SFC_WALL_WIDTH = prove
 (`forall d t. c977cc_normal d t ==> t + (&14 / &25) * d < &138 / &125`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= (d - t) * (&1129 * d - &271 * t)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 <= (t + (&14 / &25) * d - &138 / &125) * (t + (&14 / &25) * d + &138 / &125)` THEN
  RASM_ARITH_TAC);;

(* Lean: close_order *)
let C1092SFC_CLOSE_ORDER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\
             &0 <= c1092prs_sigma c s d t
             ==> &49 / &50 < c1092prs_kappa c s d t /\ c1092prs_sigma c s d t < &3 / &20`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092UTS_COSINE_CAP) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092PRS_RELATIVE_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092PRS_RELATIVE_UNIT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `c1092prs_sigma c s d t < &3 / &20` ASSUME_TAC THENL
  [REWRITE_TAC[c1092prs_sigma] THEN
   C1092PRS_PROD `&0 <= s * (d - t)` THEN
   C1092PRS_PROD `&0 <= t * (&1 / &5 - (c - s))` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 < (&3 / &20 - c1092prs_sigma c s d t) * (&3 / &20 + c1092prs_sigma c s d t)` THEN
  C1092PRS_PROD `&0 <= (&49 / &50 - c1092prs_kappa c s d t) * (&49 / &50 + c1092prs_kappa c s d t)` THEN
  RASM_ARITH_TAC);;

(* Lean: earlier_weight *)
let C1092SFC_EARLIER_WEIGHT = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ c1092prs_sigma c s d t <= &0
     ==> &11 / &25 <= (&11 / &25) * c1092prs_kappa c s d t - c1092prs_sigma c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092PRS_RELATIVE_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092PRS_RELATIVE_UNIT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092PRS_PROD `&0 <= c1092prs_kappa c s d t * --c1092prs_sigma c s d t` THEN
  SUBGOAL_THEN `&1 <= c1092prs_kappa c s d t - c1092prs_sigma c s d t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 < (&1 - (c1092prs_kappa c s d t - c1092prs_sigma c s d t)) *
                       (&1 + (c1092prs_kappa c s d t - c1092prs_sigma c s d t))` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;
