(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NortheastSignScalars.lean            *)
(* (namespace N12Compact.C1092MMMPNortheastSignScalars).                     *)
(* Normal is c977cc_normal; normal_bounds is C977CC_NORMAL_BOUNDS.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092MNSS_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)
    else NO_TAC));;

(* Lean: longitudinal *)
let C1092MNSS_LONGITUDINAL = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t
     ==> b * (&27 / &20 - d - r + (&13 / &20) * d * r - (&37 / &50) * r pow 2) +
         t * (&2 + r - d - (&37 / &50) * d * r - (&13 / &20) * r pow 2) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNSS_NORMAL_TAC THEN
  ABBREV_TAC `FF = &27 / &20 - d - r + (&13 / &20) * d * r - (&37 / &50) * r pow 2` THEN
  ABBREV_TAC `GG = &2 + r - d - (&37 / &50) * d * r - (&13 / &20) * r pow 2` THEN
  SUBGOAL_THEN `&0 <= d * r /\ &0 <= (&1 - d) * ((&6 / &5) * (&1 + d) - &2) /\
                &0 <= r * (&1 - d)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FF + GG <= &27 / &20 /\ FF <= GG` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN CONJ_TAC THEN
    NLIN_TAC [SQ_NONNEG `r:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (b - t) * (GG - FF) /\ &0 <= (b + t) * (&27 / &20 - (FF + GG))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: coefficient_bounds (private) *)
let C1092MNSS_COEFFICIENT_BOUNDS = prove
 (`forall b t. c977cc_normal b t /\ &9 / &20 < t /\ b < &9 / &10
     ==> &19 / &200 < b + t - &1 - (&61 / &100) * b * t /\
         b + t - &1 - (&61 / &100) * b * t < &1 /\
         &49 / &200 < &1 - b + t - (&61 / &100) * t pow 2 /\
         &1 - b + t - (&61 / &100) * t pow 2 <= &139 / &200`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNSS_NORMAL_TAC THEN
  SUBGOAL_THEN `&67 / &50 < b + t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (t - &9 / &20) * (b - &9 / &20) /\
                  &0 <= (&67 / &50 - (b + t)) * (&67 / &50 + b + t - &9 / &10)`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (b + t - &67 / &50) * (&1 - (&61 / &200) * (b + t + &67 / &50)) /\
    &0 <= b * t /\ &0 <= (b - t) * (b + t) /\
    &0 <= (b - t) * (&1 - (&61 / &200) * (b + t))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t pow 2 <= &1 / &2` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* Lean: short_projection (private) *)
let C1092MNSS_SHORT_PROJECTION = prove
 (`forall d r A B. d pow 2 + r pow 2 = &1 /\ &0 < A /\ A < &181 / &200 /\
             --(&61 / &200) <= B /\ B <= &61 / &200
             ==> d * A + r * B < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d * A + r * B) pow 2 + (r * A - d * B) pow 2 = A pow 2 + B pow 2`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `(d * A + r * B) pow 2 + (r * A - d * B) pow 2 =
                  (d pow 2 + r pow 2) * (A pow 2 + B pow 2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_LID]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&181 / &200 - A) * (&181 / &200 + A) /\
                &0 <= (&61 / &200 - B) * (&61 / &200 + B)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(d * A + r * B) pow 2 < &1` MP_TAC THENL
   [MP_TAC(SPEC `r * A - d * B` REAL_LE_POW_2) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`d * A + r * B`,`x:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  NLIN_TAC [SQ_NONNEG `x - &1`]);;

(* Lean: transverse *)
let C1092MNSS_TRANSVERSE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &9 / &20 < t /\ b < &9 / &10
     ==> --d * (b + t - &1 - (&61 / &100) * b * t) +
         r * (&1 - b + t - (&61 / &100) * t pow 2) < &1 + (&39 / &100) * r - d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C1092MNSS_COEFFICIENT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `&1 - (b + t - &1 - (&61 / &100) * b * t)`;
                `(&1 - b + t - (&61 / &100) * t pow 2) - &39 / &100`]
    C1092MNSS_SHORT_PROJECTION) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;
