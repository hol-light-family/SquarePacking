(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCenteredPositiveHeightScalars.lean    *)
(* (namespace N12Compact.C1092MPPMCenteredPositive).  The three scalar       *)
(* support margins of CENTERED-POSITIVE-INWARD-ENDING sections 7--8.         *)
(* Normal: c977cc_normal; dot_strict: C1092IFCS_DOT_STRICT.  Tag C1092CPHS_. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCapScalars.ml";;

let C1092CPHS_LIN = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: positive_own_margin *)
let C1092CPHS_POSITIVE_OWN_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &99 / &100 < c /\ s < &7 / &50
     ==> &0 < &1 - (&543 / &500) * b - r + (c * r - s * b) * (&1 - (&7 / &50) * c + s / &2) +
              (c * b + s * r) * (&17 / &125 + s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= (&1 - c) * (&1 + c - &100 / &51)` THEN
  SUBGOAL_THEN `&1 - c <= (&51 / &100) * s pow 2` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= s * (&7 / &50 - s)` THEN
  C1092PRS_PROD `&0 <= s * (c - &99 / &100)` THEN
  C1092PRS_PROD `&0 <= s * c` THEN
  ABBREV_TAC `P = &543 / &500 - (&17 / &125) * c + s - (&57 / &50) * c * s + s pow 2 / &2` THEN
  ABBREV_TAC `Q = &1 - c + &7 / &50 - (&57 / &50) * s pow 2 - c * s / &2 - (&17 / &125) * s` THEN
  SUBGOAL_THEN `P <= &19 / &20` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `Q <= &7 / &50` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `&19 / &20`; `&7 / &50`; `&1`] C1092IFCS_DOT_STRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  C1092PRS_PROD `&0 <= b * (&19 / &20 - P)` THEN
  C1092PRS_PROD `&0 <= r * (&7 / &50 - Q)` THEN
  SUBGOAL_THEN
   `&1 - (&543 / &500) * b - r + (c * r - s * b) * (&1 - (&7 / &50) * c + s / &2) +
    (c * b + s * r) * (&17 / &125 + s) = &1 - P * b - Q * r` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_right_margin *)
let C1092CPHS_NEGATIVE_RIGHT_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &99 / &100 < c /\ s < &7 / &50
     ==> &43 / &500 < (c * b - s * r) * (&17 / &125 + s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 < (c - &99 / &100) * (&17 / &125 + s)` THEN
  C1092PRS_PROD `&0 <= s * (&427 / &500 - s)` THEN
  SUBGOAL_THEN `&1683 / &12500 < (c - s) * (&17 / &125 + s)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 < b * ((c - s) * (&17 / &125 + s) - &1683 / &12500)` THEN
  C1092PRS_PROD `&0 <= (s * (b - r)) * (&17 / &125 + s)` THEN
  RASM_ARITH_TAC);;

(* Lean: negative_left_margin *)
let C1092CPHS_NEGATIVE_LEFT_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &99 / &100 < c
     ==> &0 < (&43 / &50) * (c * b - s * r) + (c * r + s * b) * (&17 / &125 + s) -
              (&7 / &20) * (b + r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `&2507 / &5000 < (&43 / &50) * c + (&17 / &125) * s + s pow 2 - &7 / &20`
    ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= s * (c - &43 / &50)` THEN
  SUBGOAL_THEN `--(&673 / &3125) < (&17 / &125) * c + s * (c - &43 / &50) - &7 / &20`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 < b * (((&43 / &50) * c + (&17 / &125) * s + s pow 2 - &7 / &20) -
                           &2507 / &5000)` THEN
  C1092PRS_PROD `&0 <= r * (((&17 / &125) * c + s * (c - &43 / &50) - &7 / &20) +
                           &673 / &3125)` THEN
  C1092PRS_PROD `&0 <= (b - r) * (&673 / &3125)` THEN
  RASM_ARITH_TAC);;

(* Lean: positive_coefficients_upper *)
let C1092CPHS_POSITIVE_COEFFICIENTS_UPPER = prove
 (`forall b r. c977cc_normal b r
     ==> r pow 2 + b - r - (&43 / &500) * b * r <= &1 /\ r pow 2 + b - r <= &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= r * (&1 - r)` THEN
  C1092PRS_PROD `&0 <= b * r` THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: negative_coefficient_upper *)
let C1092CPHS_NEGATIVE_COEFFICIENT_UPPER = prove
 (`forall b r. c977cc_normal b r ==> b pow 2 - (&43 / &500) * b * r - b + r <= &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= b * (&1 - b)` THEN
  C1092PRS_PROD `&0 <= b * r` THEN
  RASM_ARITH_TAC);;
