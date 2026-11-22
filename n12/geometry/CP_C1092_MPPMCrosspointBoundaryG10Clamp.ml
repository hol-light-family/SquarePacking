(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryG10Clamp.lean       *)
(* (N12Compact.C1092MPPMCrosspointSupport).  The clamped C support from      *)
(* BOUNDARY-SCALARS section 5.  Normal is c977cc_normal; FC, kC, deltaC,     *)
(* Quarter are c1092mcs_*; canonical_bounds C1092PRS_CANONICAL_BOUNDS;       *)
(* cosine_cap C1092UTS_COSINE_CAP; dot_le_one C977CSB_DOT_LE_ONE.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointSupportScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveSuccessorFarCapScalars.ml";;

let C1092G10_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: steep_bounds *)
let C1092G10_STEEP_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &3 / &5 <= s
         ==> c <= &4 / &5 /\ s < &71 / &100 /\ &7 / &5 <= c + s /\ c + s < &14143 / &10000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092UTS_COSINE_CAP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092PRS_NORMAL_TAC THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092PRS_PROD `&0 <= (s - &3 / &5) * (&4 / &5 - s)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN C1092PRS_PROD `&0 < (&7 / &5 - s - c) * (&7 / &5 - s + c)` THEN C1092G10_LP_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 <= (c + s - &14143 / &10000) * (c + s + &14143 / &10000)` THEN
   C1092PRS_PROD `&0 <= (c - s) * (c - s)` THEN C1092G10_LP_TAC]);;

(* Lean: FC_lower_formula *)
let C1092G10_FC_LOWER_FORMULA = prove
 (`forall c s h r. c977cc_normal c s /\ c1092mcs_deltaC c s h r <= &0
     ==> c1092mcs_FC c s h r =
         (--c - s + (&293 / &500) * c * s) * h +
         (c - s + c pow 2 / &2 + (&543 / &500) * s pow 2) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= c1092mcs_deltaC c s h r` THEN
  ASM_REWRITE_TAC[c1092mcs_FC] THENL
  [SUBGOAL_THEN `c1092mcs_deltaC c s h r = &0` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[c1092mcs_kC; c1092mcs_deltaC] THEN CONV_TAC REAL_RING;
   REWRITE_TAC[c1092mcs_kC; c1092mcs_deltaC] THEN REAL_ARITH_TAC]);;

(* Lean: FC_upper_formula *)
let C1092G10_FC_UPPER_FORMULA = prove
 (`forall c s h r. c977cc_normal c s /\ &0 <= c1092mcs_deltaC c s h r
     ==> c1092mcs_FC c s h r =
         (--c + s + (&43 / &500) * c * s - s pow 2) * h +
         (&1 + (&43 / &500) * s pow 2 + c * s - c - s) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[c1092mcs_FC] THEN
  UNDISCH_TAC `c977cc_normal c s` THEN
  REWRITE_TAC[c977cc_normal; c1092mcs_kC; c1092mcs_deltaC] THEN STRIP_TAC THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: FC_low_cap *)
let C1092G10_FC_LOW_CAP = prove
 (`forall c s h r. c977cc_normal c s /\ &3 / &5 <= s /\ c1092mcs_quarter h r /\
             &4 / &5 <= h /\ r <= &3 / &5
             ==> c1092mcs_FC c s h r <= --(&3496 / &3125) * h + (&11387 / &12500) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mcs_quarter x y`) (concl th))) THEN
  C1092PRS_PROD `&0 <= c * (&3 / &5 - r)` THEN
  C1092PRS_PROD `&0 <= s * (h - &4 / &5)` THEN
  SUBGOAL_THEN `c1092mcs_deltaC c s h r <= &0` ASSUME_TAC THENL
  [REWRITE_TAC[c1092mcs_deltaC] THEN C1092G10_LP_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[C1092G10_FC_LOWER_FORMULA] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092PRS_PROD `&0 <= (c + s - &7 / &5) * --(--(&1) + (&293 / &1000) * (c + s + &7 / &5))` THEN
  C1092PRS_PROD `&0 <= (s - &3 / &5) * (&1 - (&293 / &500) * (s + &3 / &5))` THEN
  SUBGOAL_THEN `--c - s + (&293 / &500) * c * s <= --(&3496 / &3125) /\
                c - s + (c * c) / &2 + (&543 / &500) * s * s <= &11387 / &12500`
  STRIP_ASSUME_TAC THENL [C1092G10_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (--(&3496 / &3125) - (--c - s + (&293 / &500) * c * s)) * h` THEN
  C1092PRS_PROD `&0 <= (&11387 / &12500 - (c - s + (c * c) / &2 + (&543 / &500) * s * s)) * r` THEN
  C1092G10_LP_TAC);;

(* Lean: FC_middle_cap *)
let C1092G10_FC_MIDDLE_CAP = prove
 (`forall c s h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal h r /\ &3 / &5 <= r
             ==> c1092mcs_FC c s h r <= (&543 / &500) * r - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092PRS_PROD `&0 < c * h` THEN C1092PRS_PROD `&0 <= s * r` THEN
  SUBGOAL_THEN `(c * h + s * r) * (c * h + s * r) + (c * r - s * h) * (c * r - s * h) = &1 /\
                r = (c * h + s * r) * s + (c * r - s * h) * c` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `h * h + r * r = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (c * h + s * r) * (&1 - (c * h + s * r))` THEN
  REWRITE_TAC[c1092mcs_FC; c1092mcs_kC; c1092mcs_deltaC] THEN
  COND_CASES_TAC THENL
  [C1092PRS_PROD `&0 <= s * (h - r)` THEN
   C1092PRS_PROD `&0 <= r * (&1 / &5 - (c - s))` THEN
   SUBGOAL_THEN `c * r - s * h < &3 / &20` ASSUME_TAC THENL [C1092G10_LP_TAC; ALL_TAC] THEN
   C1092PRS_PROD `&0 <= (c * r - s * h) * (&3 / &20 - (c * r - s * h))` THEN
   SUBGOAL_THEN `&1 - (c * h + s * r) <= (&3 / &20) * (c * r - s * h)` ASSUME_TAC THENL
   [C1092G10_LP_TAC; ALL_TAC] THEN
   C1092PRS_PROD `&0 <= (c * r - s * h) * (&17 / &20 + (&43 / &500) * c - s)` THEN
   C1092G10_LP_TAC;
   SUBGOAL_THEN `c * r - s * h <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092PRS_PROD `&0 <= r * (c - s)` THEN
   C1092PRS_PROD `&0 <= s * (&1 / &5 - (h - r))` THEN
   SUBGOAL_THEN `--(c * r - s * h) < &3 / &20` ASSUME_TAC THENL [C1092G10_LP_TAC; ALL_TAC] THEN
   C1092PRS_PROD `&0 <= --(c * r - s * h) * (&3 / &20 + (c * r - s * h))` THEN
   SUBGOAL_THEN `&1 - (c * h + s * r) <= --(&3 / &20) * (c * r - s * h)` ASSUME_TAC THENL
   [C1092G10_LP_TAC; ALL_TAC] THEN
   C1092PRS_PROD `&0 <= --(c * r - s * h) * (&17 / &20 - (&293 / &500) * c)` THEN
   C1092G10_LP_TAC]);;

(* Lean: FC_high_cap *)
let C1092G10_FC_HIGH_CAP = prove
 (`forall c s h r. c977cc_normal c s /\ &3 / &5 <= s /\ c1092mcs_quarter h r /\ h <= r
             ==> c1092mcs_FC c s h r <= --(&457 / &1000) * h + (&129 / &1000) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mcs_quarter x y`) (concl th))) THEN
  C1092PRS_PROD `&0 <= (c - s) * r` THEN C1092PRS_PROD `&0 <= s * (r - h)` THEN
  SUBGOAL_THEN `&0 <= c1092mcs_deltaC c s h r` ASSUME_TAC THENL
  [REWRITE_TAC[c1092mcs_deltaC] THEN C1092G10_LP_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[C1092G10_FC_UPPER_FORMULA] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092PRS_PROD `&0 <= (c - s) * (&1 - (c + s) / &2)` THEN
  C1092PRS_PROD `&0 <= (c - s) * (c - s)` THEN
  C1092PRS_PROD `&0 <= (&14143 / &10000 - (c + s)) * (&14143 / &10000 + (c + s) - &2)` THEN
  C1092PRS_PROD `&0 <= (c - s) * (c + s)` THEN
  SUBGOAL_THEN `--c + s + (&43 / &500) * c * s - s * s <= --(&457 / &1000) /\
                &1 + (&43 / &500) * s * s + c * s - c - s <= &129 / &1000`
  STRIP_ASSUME_TAC THENL [C1092G10_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (--(&457 / &1000) - (--c + s + (&43 / &500) * c * s - s * s)) * h` THEN
  C1092PRS_PROD `&0 <= (&129 / &1000 - (&1 + (&43 / &500) * s * s + c * s - c - s)) * r` THEN
  C1092G10_LP_TAC);;
