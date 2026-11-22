(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryG10.lean            *)
(* (N12Compact.C1092MPPMCrosspointSupport).  The complete G10 boundary       *)
(* inequality.  Normal is c977cc_normal; G10, G00, FC, Quarter are           *)
(* c1092mcs_*; G10Low / G10Clamp results C1092G10L_ / C1092G10_*;            *)
(* canonical_bounds C1092PRS_CANONICAL_BOUNDS; norm_le C1092NPP_NORM_LE.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG10Low.ml";;

let C1092G10F_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092G10F_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092G10F_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092G10F_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: G10_high_nonnegative *)
let C1092G10F_G10_HIGH_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c1092mcs_quarter h r /\ h <= r
                 ==> &0 <= c1092mcs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092G10_FC_HIGH_CAP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092G10F_NORMAL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mcs_quarter x y`) (concl th))) THEN
  SUBGOAL_THEN `h * h + r * r = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092G10F_PROD `&0 <= (r - h) * (h + r)` THEN
  SUBGOAL_THEN `&7 / &10 < r` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092G10F_PROD `&0 <= (&7 / &10 - r) * (&7 / &10 + r)` THEN C1092G10F_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r <= &1` ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `h:real`]; ALL_TAC] THEN
  C1092G10F_PROD `&0 <= (d - t) * r` THEN C1092G10F_PROD `&0 <= t * (r - h)` THEN
  SUBGOAL_THEN `&0 <= c1092mcs_deltaE d t h r` ASSUME_TAC THENL
  [REWRITE_TAC[c1092mcs_deltaE] THEN C1092G10F_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092G10L_G10_UPPER_FORMULA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092G10F_PROD `&0 <= ((--(&457 / &1000) * h + (&129 / &1000) * r) - c1092mcs_FC c s h r) * d` THEN
  ABBREV_TAC `P = &1 + h * r - (&1543 / &1000) * h - (&1129 / &1000) * r` THEN
  ABBREV_TAC `Q = r * r - (&36 / &25) * r` THEN
  SUBGOAL_THEN `P * d + Q * t + r <= c1092mcs_G10 c s d t h r` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
   C1092G10F_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Q <= &0` ASSUME_TAC THENL
  [EXPAND_TAC "Q" THEN C1092G10F_PROD `&0 <= r * (&36 / &25 - r)` THEN C1092G10F_LP_TAC;
   ALL_TAC] THEN
  C1092G10F_PROD `&0 <= h * (r - h)` THEN
  SUBGOAL_THEN `&1 <= r + (&3 / &5) * h` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092G10F_PROD `&0 < (&1 - (r + (&3 / &5) * h)) * (&1 + (r + (&3 / &5) * h))` THEN
   C1092G10F_PROD `&0 <= h * h` THEN C1092G10F_LP_TAC; ALL_TAC] THEN
  C1092G10F_PROD `&0 <= h * (r + (&3 / &5) * h - &1)` THEN
  SUBGOAL_THEN `&0 < P - Q` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN NLIN_TAC [SQ_NONNEG `h - &543 / &800`]; ALL_TAC] THEN
  C1092G10F_PROD `&0 <= (P - Q) * (d - t)` THEN
  ASM_CASES_TAC `&0 <= P + Q` THENL
  [C1092G10F_PROD `&0 <= (P + Q) * (d + t)` THEN C1092G10F_LP_TAC;
   C1092G10F_PROD `&0 <= --(P + Q) * (&71 / &50 - (d + t))` THEN
   SUBGOAL_THEN `&71 / &50 - (&11 / &10) * h - (&83 / &100) * r <= r + (&71 / &100) * (P + Q)`
   ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN C1092G10F_LP_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`&11 / &10`; `&83 / &100`; `h:real`; `r:real`; `&7 / &5`] C1092NPP_NORM_LE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
   C1092G10F_LP_TAC]);;

(* Lean: G10_middle_nonnegative *)
let C1092G10F_G10_MIDDLE_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c977cc_normal h r /\ &3 / &5 <= r /\ &0 <= c1092mcs_G00 h r d t h r
                 ==> &0 <= c1092mcs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092G10_FC_MIDDLE_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092G10F_NORMAL_TAC THEN
  C1092G10F_PROD `&0 <= d * ((&543 / &500) * r - &1 - c1092mcs_FC c s h r)` THEN
  SUBGOAL_THEN `c1092mcs_G10 c s d t h r - c1092mcs_G00 h r d t h r =
                d * ((&543 / &500) * r - &1 - c1092mcs_FC c s h r)` ASSUME_TAC THENL
  [REWRITE_TAC[c1092mcs_G10; c1092mcs_G00; c1092mcs_k; c1092mcs_kC; c1092mcs_deltaC;
               c1092mcs_kE; c1092mcs_C0; REAL_ARITH `h * r - r * h = &0`; REAL_ABS_0] THEN
   UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092G10F_LP_TAC);;

(* Lean: G10_nonnegative *)
let C1092G10F_G10_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c1092mcs_quarter h r /\
                 (forall a b. c977cc_normal a b ==> &3 / &5 <= b ==> &0 <= c1092mcs_G00 a b d t a b)
                 ==> &0 <= c1092mcs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mcs_quarter x y`) (concl th))) THEN
  ASM_CASES_TAC `r <= &3 / &5` THENL
  [MATCH_MP_TAC C1092G10L_G10_LOW_NONNEGATIVE THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092G10F_PROD `&0 <= (&3 / &5 - r) * (&3 / &5 + r)` THEN
   C1092G10F_PROD `&0 < (&4 / &5 - h) * (&4 / &5 + h)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092G10F_LP_TAC;
   ASM_CASES_TAC `h <= r` THENL
   [MATCH_MP_TAC C1092G10F_G10_HIGH_NONNEGATIVE THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `c977cc_normal h r /\ &3 / &5 <= r` STRIP_ASSUME_TAC THENL
    [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC C1092G10F_G10_MIDDLE_NONNEGATIVE THEN ASM_MESON_TAC[]]]);;
