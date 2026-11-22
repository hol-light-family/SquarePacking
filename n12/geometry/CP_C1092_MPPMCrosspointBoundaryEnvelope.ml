(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryEnvelope.lean       *)
(* (N12Compact.C1092MPPMCrosspointSupport), BOUNDARY-SCALARS Lemma 2.        *)
(* Normal is c977cc_normal; FE, kE, deltaE, E0, Quarter are c1092mcs_*;      *)
(* FE_before_aligned_cap C1092MCBA_FE_BEFORE_ALIGNED_CAP; dot_le_one         *)
(* C977CSB_DOT_LE_ONE; UnitCircleChord CCUCC_*.  Lean a, j, A, B are         *)
(* written out (kE, deltaE and the two coefficients).                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryAligned.ml";;

let C1092MCBEV_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MCBEV_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092MCBEV_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

(* Lean: FE_low_cap *)
let C1092MCBEV_FE_LOW_CAP = prove
 (`forall d t h r. c977cc_normal d t /\ c1092mcs_quarter h r /\ &4 / &5 <= h /\ r <= &3 / &5
     ==> c1092mcs_FE d t h r <= h - (&14 / &25) * r - &1 + &1 / &3125`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mcs_quarter x y`) (concl th))) THEN
  SUBGOAL_THEN `c977cc_normal h r` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r <= t` THENL
  [MP_TAC(SPECL [`h:real`; `r:real`; `d:real`; `t:real`] C1092MCBA_FE_BEFORE_ALIGNED_CAP) THEN
   ASM_REWRITE_TAC[c1092mcs_E0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t <= r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MCBC_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C977CSB_DOT_LE_ONE) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] CCUCC_CROSS_ORDER) THEN
  MP_TAC(SPECL [`&1`; `&0`; `h:real`; `r:real`; `d:real`; `t:real`;
                `--h`; `h:real`; `r:real`] CCUCC_LINEAR_NONNEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
   C1092MCBEV_LP_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c1092mcs_FE d t h r - (h - (&14 / &25) * r - &1) =
     &1 - (d * h + t * r) + (d * r - t * h) * (d * h + t * r) * ((&3 / &5) * r - (&11 / &25) * h) -
     (d * r - t * h) pow 2 * ((&3 / &5) * h + (&11 / &25) * r)` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= c1092mcs_deltaE d t h r` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c1092mcs_deltaE]; ALL_TAC] THEN
   ASM_REWRITE_TAC[c1092mcs_FE] THEN
   REWRITE_TAC[c1092mcs_kE; c1092mcs_deltaE; c1092mcs_E0] THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(d * h + t * r) pow 2 + (d * r - t * h) pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092MCBEV_PROD `&0 <= (&1 - (d * h + t * r)) * ((d * h + t * r) - &4 / &5)` THEN
  SUBGOAL_THEN `&1 - (d * h + t * r) <= (&5 / &9) * ((d * r - t * h) * (d * r - t * h))`
  ASSUME_TAC THENL [C1092MCBEV_LP_TAC; ALL_TAC] THEN
  C1092MCBEV_PROD `&0 <= r * ((&1 + h) / &3 - r)` THEN
  SUBGOAL_THEN `&1 - r / &3 <= h` ASSUME_TAC THENL
  [MP_TAC(SPECL [`&1 + h`; `h - &1 + r / &3`] C1092MCBA_CANCEL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN C1092MCBEV_LP_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_CASES_TAC `(&3 / &5) * r - (&11 / &25) * h <= &0` THENL
  [C1092MCBEV_PROD `&0 <= ((d * r - t * h) * (d * h + t * r)) * --((&3 / &5) * r - (&11 / &25) * h)` THEN
   C1092MCBEV_PROD `&0 <= ((d * r - t * h) * (d * r - t * h)) *
                          (((&3 / &5) * h + (&11 / &25) * r) - &5 / &9)` THEN
   C1092MCBEV_LP_TAC;
   SUBGOAL_THEN `&1 / &2 <= r` ASSUME_TAC THENL [C1092MCBEV_LP_TAC; ALL_TAC] THEN
   C1092MCBEV_PROD `&0 <= (d * r - t * h) * (&1 / &125 - ((&3 / &5) * r - (&11 / &25) * h))` THEN
   C1092MCBEV_PROD `&0 <= ((d * r - t * h) * ((&3 / &5) * r - (&11 / &25) * h)) *
                          (&1 - (d * h + t * r))` THEN
   C1092MCBEV_PROD `&0 <= ((d * r - t * h) * (d * r - t * h)) *
                          (((&3 / &5) * h + (&11 / &25) * r) - (&5 / &9 + &1 / &20))` THEN
   C1092MCBEV_PROD `&0 <= ((d * r - t * h) - &2 / &25) * ((d * r - t * h) - &2 / &25)` THEN
   C1092MCBEV_LP_TAC]);;
