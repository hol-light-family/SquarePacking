(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeOwnedPositiveCeilingScalars  *)
(* .lean (N12Compact.C1092MPPMNegativeOwnedPositiveCeiling.Scalars).         *)
(* NEGATIVE-OWNED-POSITIVE-CEILING, exact full-arc scalar margins.          *)
(* Normal is c977cc_normal; norm_lt is C1092NPP_NORM_LT; quarter_data is     *)
(* C1092WPS_QUARTER_DATA (the half angle s/(1+c)); the cosH/sinH rewriting   *)
(* of the Lean proof is replaced by the equivalent half-angle relations.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveNegativeRetainingScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C1092ShallowPositiveScalars.ml";;

let C1092NOPC_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: P0, Q0, P1, Q1, quartic (definitions) *)
let c1092nopc_P0 = new_definition
 `c1092nopc_P0 (b:real) (r:real) =
    b + r - &13 / &50 - (&7 / &20) * b pow 2 - (&13 / &20) * b * r`;;
let c1092nopc_Q0 = new_definition
 `c1092nopc_Q0 (b:real) (r:real) = b - r - b pow 2 + (&7 / &20) * r * (b - r)`;;
let c1092nopc_P1 = new_definition
 `c1092nopc_P1 (c:real) (s:real) = &1 - c + c pow 2 - (&7 / &50) * c * s`;;
let c1092nopc_Q1 = new_definition
 `c1092nopc_Q1 (c:real) (s:real) = s - c * s + &13 / &50 + (&7 / &50) * s pow 2`;;
let c1092nopc_quartic = new_definition
 `c1092nopc_quartic (x:real) =
    -- &20169 * x pow 4 - &9400 * x pow 3 + &8738 * x pow 2 + &1400 * x - &169`;;

(* Lean: own_margin *)
let C1092NOPC_OWN_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &87 / &100 < b
     ==> &0 < c * c1092nopc_P0 b r + s * c1092nopc_Q0 b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REWRITE_TAC[c1092nopc_P0; c1092nopc_Q0; REAL_POW_2] THEN
  C1092PRS_PROD `&0 <= r * (&1 - b + r)` THEN
  C1092PRS_PROD `&0 <= r * (&13 / &20 - r / &2)` THEN
  C1092PRS_PROD `&0 <= (&1 - b) * (&1 - b)` THEN
  SUBGOAL_THEN `b - r - b * b + (&7 / &20) * r * (b - r) <= &0` ASSUME_TAC THENL
  [C1092NOPC_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (b - r) * (b - r)` THEN
  C1092PRS_PROD `&0 < (&13 / &100 - (&1 - b)) * (&13 / &100 + (&1 - b))` THEN
  SUBGOAL_THEN `&11 / &50 < (b + r - &13 / &50 - (&7 / &20) * b * b - (&13 / &20) * b * r) +
                            (b - r - b * b + (&7 / &20) * r * (b - r))` ASSUME_TAC THENL
  [C1092NOPC_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (c - s) * --(b - r - b * b + (&7 / &20) * r * (b - r))` THEN
  C1092PRS_PROD `&0 < c * ((b + r - &13 / &50 - (&7 / &20) * b * b - (&13 / &20) * b * r) +
                           (b - r - b * b + (&7 / &20) * r * (b - r)))` THEN
  C1092NOPC_LP_TAC);;

(* Lean: quartic_positive *)
let C1092NOPC_QUARTIC_POSITIVE = prove
 (`forall x. &11 / &100 <= x /\ x <= &5 / &12 ==> &0 < c1092nopc_quartic x`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092nopc_quartic] THEN
  C1092PRS_PROD `&0 <= (&5 / &12 - x) * (&5 / &12 + x)` THEN
  SUBGOAL_THEN `&1250 <= &8738 - &9400 * x - &20169 * x pow 2` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN C1092NOPC_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= ((&8738 - &9400 * x - &20169 * x pow 2) - &1250) * x pow 2` THEN
  C1092PRS_PROD `&0 <= (x - &11 / &100) * (x + &11 / &100)` THEN
  C1092NOPC_LP_TAC);;

(* the half-angle form of the norm defect (identity step of last_margin) *)
let C1092NOPC_LAST_IDENTITY = prove
 (`forall c s x. (&1 + x pow 2) * c = &1 - x pow 2 /\ (&1 + x pow 2) * s = &2 * x
     ==> &2500 * (&1 + x pow 2) pow 2 *
         (&1 - c1092nopc_P1 c s pow 2 - c1092nopc_Q1 c s pow 2) = c1092nopc_quartic x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c = (&1 - x pow 2) / (&1 + x pow 2) /\ s = (&2 * x) / (&1 + x pow 2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
  [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092nopc_P1; c1092nopc_Q1; c1092nopc_quartic] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 < x ==> ~(x = &0)`)) THEN
  CONV_TAC REAL_FIELD);;

(* Lean: last_margin *)
let C1092NOPC_LAST_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &11 / &100 <= s / (&1 + c)
     ==> &0 < &1 - c1092nopc_P1 c s * b - c1092nopc_Q1 c s * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NOPC_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half c s <= &5 / &12` MP_TAC THENL
  [REWRITE_TAC[C1092WPS_half] THEN
   SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [C1092NOPC_LP_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN C1092NOPC_LP_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&11 / &100 <= s / (&1 + c)` THEN REWRITE_TAC[GSYM C1092WPS_half] THEN
  SPEC_TAC(`C1092WPS_half c s`,`x:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `x:real`] C1092NOPC_LAST_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` C1092NOPC_QUARTIC_POSITIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1092nopc_P1 c s`; `c1092nopc_Q1 c s`; `b:real`; `r:real`; `&1`]
    C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &2500 * (&1 + x pow 2) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (&2500 * (&1 + x pow 2) pow 2) *
     --(&1 - c1092nopc_P1 c s pow 2 - c1092nopc_Q1 c s pow 2)` THEN
  C1092NOPC_LP_TAC);;
