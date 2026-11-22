(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointCentral.lean        *)
(* (N12Compact.C1092MPPMNegativeCrosspointSupport), NEGATIVE-WALL-SCALARS   *)
(* section 2.  Normal is c977cc_normal; ell, kC, kE, deltaC, deltaE, C0, E0, *)
(* width, G00, Quarter are c1092mncs_*; CrosspointSupport.steep_bounds is    *)
(* C1092G10_STEEP_BOUNDS; UnitCircleChord CCUCC_*.                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointSupportScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG10Clamp.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

let C1092MNCC_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MNCC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092MNCC_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092MNCC_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: shallow_bounds *)
let C1092MNCC_SHALLOW_BOUNDS = prove
 (`forall d t. c977cc_normal d t /\ &8 * t <= &3 * d ==> &93 / &100 <= d /\ t <= &9 / &25`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCC_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092MNCC_PROD `&0 <= (&3 * d - &8 * t) * (&3 * d + &8 * t)` THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
  [C1092MNCC_PROD `&0 < (&93 / &100 - d) * (&93 / &100 + d)`;
   C1092MNCC_PROD `&0 < (t - &9 / &25) * (t + &9 / &25)`] THEN
  C1092MNCC_LP_TAC);;

(* Lean: endpoint_C (private) *)
let C1092MNCC_ENDPOINT_C = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\ &8 * t <= &3 * d
     ==> &0 <= c1092mncs_ell c s d t * (c + s - &1) - s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MNCC_NORMAL_TAC THEN
  REWRITE_TAC[c1092mncs_ell] THEN
  C1092MNCC_PROD `&0 <= c * t` THEN C1092MNCC_PROD `&0 <= s * d` THEN
  C1092MNCC_PROD `&0 <= (c * t + s * d) * (c + s - &7 / &5)` THEN
  C1092MNCC_PROD `&0 <= (&3 * d / &8 - t) * (s - (&2 / &5) * c)` THEN
  C1092MNCC_PROD `&0 <= d * (s / &40 + (&3 / &20) * c)` THEN
  C1092MNCC_LP_TAC);;

(* Lean: endpoint_E (private) *)
let C1092MNCC_ENDPOINT_E = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &8 * t <= &3 * d
     ==> &0 <= c1092mncs_ell c s d t * (d + t - &1) - s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MNCC_SHALLOW_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MNCC_NORMAL_TAC THEN
  REWRITE_TAC[c1092mncs_ell] THEN
  C1092MNCC_PROD `&0 <= (c - s) * (&1 + d - t)` THEN
  C1092MNCC_PROD `&0 <= s * (&1 - &2 * t)` THEN
  SUBGOAL_THEN `&0 <= c * (&1 + d - t) - s * (d + t)` ASSUME_TAC THENL
  [C1092MNCC_LP_TAC; ALL_TAC] THEN
  C1092MNCC_PROD `&0 <= (t * t) * (c * (&1 + d - t) - s * (d + t))` THEN
  SUBGOAL_THEN `(&1 + d) * ((c * t + s * d) * (d + t - &1) - s * t) =
                (t * t) * (c * (&1 + d - t) - s * (d + t))` ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092MNCC_PROD `&0 < (&1 + d) * --((c * t + s * d) * (d + t - &1) - s * t)` THEN
  C1092MNCC_LP_TAC);;

let C1092MNCC_BELOW_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCC_NORMAL_TAC THEN
  REWRITE_TAC[c1092mncs_width; c1092mncs_ell; c1092mncs_kC; c1092mncs_kE] THEN
  C1092MNCC_PROD `&0 <= t * (abs(c1092mncs_deltaC c s h r) - c1092mncs_deltaC c s h r)` THEN
  C1092MNCC_PROD `&0 <= t * (abs(c1092mncs_deltaC c s h r) + c1092mncs_deltaC c s h r)` THEN
  C1092MNCC_PROD `&0 <= s * (abs(c1092mncs_deltaE d t h r) - c1092mncs_deltaE d t h r)` THEN
  C1092MNCC_PROD `&0 <= s * (abs(c1092mncs_deltaE d t h r) + c1092mncs_deltaE d t h r)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_deltaC; c1092mncs_deltaE]) THEN
  REWRITE_TAC[c1092mncs_deltaC; c1092mncs_deltaE] THEN C1092MNCC_LP_TAC;;

(* Lean: low_below *)
let C1092MNCC_LOW_BELOW = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t
     ==> (&2 * c1092mncs_ell c s d t + &2 * s * t) * h + &2 * s * d * r <=
         c1092mncs_width c s d t h r`,
  C1092MNCC_BELOW_TAC);;

(* Lean: middle_below *)
let C1092MNCC_MIDDLE_BELOW = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t
     ==> &2 * c1092mncs_ell c s d t * h + &2 * c1092mncs_ell c s d t * r <=
         c1092mncs_width c s d t h r`,
  C1092MNCC_BELOW_TAC);;

(* Lean: high_below *)
let C1092MNCC_HIGH_BELOW = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t
     ==> &2 * c * t * h + (&2 * c1092mncs_ell c s d t + &2 * s * t) * r <=
         c1092mncs_width c s d t h r`,
  C1092MNCC_BELOW_TAC);;

(* Lean: width_lower *)
let C1092MNCC_WIDTH_LOWER = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\
                 &8 * t <= &3 * d /\ c1092mncs_quarter h r
                 ==> &2 * c1092mncs_ell c s d t + &2 * s * t <= c1092mncs_width c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MNCC_ENDPOINT_C) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MNCC_ENDPOINT_E) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNCC_LOW_BELOW) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNCC_MIDDLE_BELOW) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNCC_HIGH_BELOW) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C1092MNCC_NORMAL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mncs_quarter x y`) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_ell]) THEN REWRITE_TAC[c1092mncs_ell] THEN
  C1092MNCC_PROD `&0 <= c * t` THEN C1092MNCC_PROD `&0 <= s * d` THEN C1092MNCC_PROD `&0 <= s * t` THEN
  SUBGOAL_THEN `r <= &1` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `h:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `t pow 2 + d pow 2 = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  let chord a b cc ss dd tt =
    MP_TAC(SPECL [cc; ss; dd; tt; `h:real`; `r:real`;
                  `--(&2 * (c * t + s * d) + &2 * s * t)`; a; b] CCUCC_LINEAR_NONNEGATIVE) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
     TRY C1092MNCC_LP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
     C1092MNCC_LP_TAC; DISCH_TAC] THEN
    C1092MNCC_LP_TAC in
  ASM_CASES_TAC `r <= s` THENL
  [chord `&2 * (c * t + s * d) + &2 * s * t` `&2 * s * d` `&1` `&0` `c:real` `s:real`;
   ASM_CASES_TAC `r <= d` THENL
   [chord `&2 * (c * t + s * d)` `&2 * (c * t + s * d)` `c:real` `s:real` `t:real` `d:real`;
    chord `&2 * c * t` `&2 * (c * t + s * d) + &2 * s * t` `t:real` `d:real` `&0` `&1`]]);;

(* Lean: G00_lower *)
let C1092MNCC_G00_LOWER = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\
                 &8 * t <= &3 * d /\ c1092mncs_quarter h r
                 ==> (&77 / &5000) * t <= c1092mncs_G00 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNCC_WIDTH_LOWER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092MNCC_NORMAL_TAC THEN
  C1092MNCC_PROD `&0 <= t * (&1 - c - (&13 / &50) * s - &77 / &5000)` THEN
  REWRITE_TAC[c1092mncs_G00; c1092mncs_C0; c1092mncs_E0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_ell]) THEN REWRITE_TAC[c1092mncs_ell] THEN
  C1092MNCC_LP_TAC);;

(* Lean: G00_nonnegative *)
let C1092MNCC_G00_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\
                 &8 * t <= &3 * d /\ c1092mncs_quarter h r
                 ==> &0 <= c1092mncs_G00 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNCC_G00_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN REAL_ARITH_TAC);;
