(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointCentral.lean *)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointSupport),                   *)
(* MISSING-NEGATIVE-WALL-SCALARS section 3.  Normal is c977cc_normal; ell,   *)
(* width, Quarter are c1092mncs_*; G00, G00star are c1092mmncs_*;            *)
(* steep_bounds C1092G10_STEEP_BOUNDS; cosine_order C977CSB_COSINE_ORDER;    *)
(* low/middle/high_below C1092MNCC_*; UnitCircleChord CCUCC_*.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointCentral.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092MMNCC_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MMNCC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092MMNCC_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

(* Lean: width_lower *)
let C1092MMNCC_WIDTH_LOWER = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\
                 &252 / &373 <= t /\ c1092mncs_quarter h r
                 ==> (&14 / &5) * c1092mncs_ell c s d t <= c1092mncs_width c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNCC_LOW_BELOW) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNCC_MIDDLE_BELOW) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNCC_HIGH_BELOW) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&3 / &5 <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `d <= &275 / &373` ASSUME_TAC THENL
  [MATCH_MP_TAC C977CSB_COSINE_ORDER THEN EXISTS_TAC `t:real` THEN
   EXISTS_TAC `&252 / &373` THEN ASM_REWRITE_TAC[c977cc_normal] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  C1092MNCC_NORMAL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mncs_quarter x y`) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_ell]) THEN REWRITE_TAC[c1092mncs_ell] THEN
  C1092MMNCC_PROD `&0 <= c * t` THEN C1092MMNCC_PROD `&0 <= s * d` THEN
  C1092MMNCC_PROD `&0 <= s * t` THEN
  C1092MMNCC_PROD `&0 <= t * (&4 * s - &3 * c)` THEN
  C1092MMNCC_PROD `&0 <= s * (&11 * t - &10 * d)` THEN
  C1092MMNCC_PROD `&0 <= (c * t + s * d) * (c + s - &7 / &5)` THEN
  C1092MMNCC_PROD `&0 <= (c * t + s * d) * (d + t - &7 / &5)` THEN
  SUBGOAL_THEN `r <= &1` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `h:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `t pow 2 + d pow 2 = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  let chord a b cc ss dd tt =
    MP_TAC(SPECL [cc; ss; dd; tt; `h:real`; `r:real`;
                  `--((&14 / &5) * (c * t + s * d))`; a; b] CCUCC_LINEAR_NONNEGATIVE) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
     TRY C1092MMNCC_LP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
     C1092MMNCC_LP_TAC; DISCH_TAC] THEN
    C1092MMNCC_LP_TAC in
  ASM_CASES_TAC `r <= s` THENL
  [chord `&2 * (c * t + s * d) + &2 * s * t` `&2 * s * d` `&1` `&0` `c:real` `s:real`;
   ASM_CASES_TAC `r <= d` THENL
   [chord `&2 * (c * t + s * d)` `&2 * (c * t + s * d)` `c:real` `s:real` `t:real` `d:real`;
    chord `&2 * c * t` `&2 * (c * t + s * d) + &2 * s * t` `t:real` `d:real` `&0` `&1`]]);;

(* Lean: G00_lower *)
let C1092MMNCC_G00_LOWER = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\
                 &252 / &373 <= t /\ c1092mncs_quarter h r
                 ==> &47 / &1000 <= c1092mmncs_G00 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MMNCC_WIDTH_LOWER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092G10_STEEP_BOUNDS) THEN
  SUBGOAL_THEN `&3 / &5 <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092MNCC_NORMAL_TAC THEN
  C1092MMNCC_PROD `&0 <= (&71 / &100 - s) * (t - &1 / &2)` THEN
  C1092MMNCC_PROD `&0 <= (s - &3 / &5) * d` THEN
  C1092MMNCC_PROD `&0 <= (c - t) * (c - t)` THEN
  C1092MMNCC_PROD `&0 <= (s - d) * (s - d)` THEN
  REWRITE_TAC[c1092mmncs_G00; c1092mncs_C0; c1092mmncs_E0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_ell; REAL_POW_2]) THEN REWRITE_TAC[c1092mncs_ell] THEN
  C1092MMNCC_LP_TAC);;

(* Lean: G00star_lower *)
let C1092MMNCC_G00STAR_LOWER = prove
 (`forall epsilon c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\
                 &252 / &373 <= t /\ c1092mncs_quarter h r /\ epsilon <= &43 / &500
                 ==> &1 / &250 <= c1092mmncs_G00star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MMNCC_G00_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MNCC_NORMAL_TAC THEN
  C1092MMNCC_PROD `&0 <= (c - s) * (c + s)` THEN
  C1092MMNCC_PROD `&0 <= (d - t) * (d + t)` THEN
  C1092MMNCC_PROD `&0 <= (s - t) * (s - t)` THEN
  C1092MMNCC_PROD `&0 <= (&43 / &500 - epsilon) * (s * t)` THEN
  REWRITE_TAC[c1092mmncs_G00star] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MMNCC_LP_TAC);;
