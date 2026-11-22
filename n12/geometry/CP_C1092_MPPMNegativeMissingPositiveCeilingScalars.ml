(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeMissingPositiveCeilingScalars*)
(* .lean (N12Compact.C1092MPPMNegativeMissingPositiveCeiling.Scalars).       *)
(* Exact full-interval inequalities with the genuine 1.086 predecessor cap.  *)
(* Normal is c977cc_normal; norm_lt is C1092NPP_NORM_LT; quarter_data is     *)
(* C1092WPS_QUARTER_DATA (the half angle s/(1+c), C1092WPS_half);            *)
(* CommonCases.UnitCircleChord.decreasing is CCUCC_DECREASING.  As in the    *)
(* sibling port CP_C1092_MPPMNegativeOwnedPositiveCeilingScalars.ml, the     *)
(* cosH/sinH rewriting is replaced by the half-angle relations, and the      *)
(* G01Quartic Bernstein bound of quartic_positive by a direct product proof. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveNegativeRetainingScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C1092ShallowPositiveScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointG01Quartic.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveCeilingScalars.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

let C1092NMPC_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: P0, Q0, P1, Q1, f2, g2, quartic (definitions) *)
let c1092nmpc_P0 = new_definition
 `c1092nmpc_P0 (b:real) (r:real) = b + r - &13 / &50 - (&21 / &25) * b * r`;;
let c1092nmpc_Q0 = new_definition
 `c1092nmpc_Q0 (b:real) (r:real) = b - r - (&13 / &50) * r pow 2 - (&11 / &10) * b pow 2`;;
let c1092nmpc_P1 = new_definition
 `c1092nmpc_P1 (c:real) (s:real) = &11 / &10 - c + c pow 2 - (&7 / &50) * c * s`;;
let c1092nmpc_Q1 = new_definition
 `c1092nmpc_Q1 (c:real) (s:real) = s - c * s + &13 / &50 + (&7 / &50) * s pow 2`;;
let c1092nmpc_f2 = new_definition
 `c1092nmpc_f2 (b:real) (r:real) = &1 + b * r - b - r + (&43 / &500) * b pow 2`;;
let c1092nmpc_g2 = new_definition
 `c1092nmpc_g2 (b:real) (r:real) = b pow 2 - b + r - (&43 / &500) * b * r`;;
let c1092nmpc_quartic = new_definition
 `c1092nmpc_quartic (x:real) =
    -- &10847 * x pow 4 - &4770 * x pow 3 + &4344 * x pow 2 + &770 * x - &347`;;

(* Lean: own_margin *)
let C1092NMPC_OWN_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ b < &33 / &40 /\ &283 / &500 < r
     ==> &0 < c * c1092nmpc_P0 b r + s * c1092nmpc_Q0 b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  REWRITE_TAC[c1092nmpc_P0; c1092nmpc_Q0] THEN
  C1092PRS_PROD `&0 <= (b - r) * (b + r)` THEN
  SUBGOAL_THEN `b - r - (&13 / &50) * r pow 2 - (&11 / &10) * b pow 2 < &0` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `r:real`]; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= b * (&10 / &7 - (b + r))` THEN
  SUBGOAL_THEN `&0 < (b + r - &13 / &50 - (&21 / &25) * b * r) +
                    (b - r - (&13 / &50) * r pow 2 - (&11 / &10) * b pow 2)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C1092PRS_PROD `&0 < c * ((b + r - &13 / &50 - (&21 / &25) * b * r) +
                    (b - r - (&13 / &50) * r pow 2 - (&11 / &10) * b pow 2))` THEN
  C1092PRS_PROD `&0 <= (c - s) * --(b - r - (&13 / &50) * r pow 2 - (&11 / &10) * b pow 2)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: coefficient_bounds *)
let C1092NMPC_COEFFICIENT_BOUNDS = prove
 (`forall b r. c977cc_normal b r /\ b < &33 / &40 /\ &23 / &50 < b * r
     ==> c1092nmpc_f2 b r < &29 / &200 /\ c1092nmpc_g2 b r < &461 / &1000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  REWRITE_TAC[c1092nmpc_f2; c1092nmpc_g2] THEN
  SUBGOAL_THEN `b + r <= &283 / &200` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `b - r:real`; SQ_NONNEG `b + r - &283 / &200`]; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (&283 / &200 - (b + r)) * (b + r + &283 / &200 - &2)` THEN
  C1092PRS_PROD `&0 < (&33 / &40 - b) * (&33 / &40 + b)` THEN
  C1092PRS_PROD `&0 <= (b - r) * (&2 - b - r)` THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: quartic_positive *)
let C1092NMPC_QUARTIC_POSITIVE = prove
 (`forall x. &7 / &24 <= x /\ x <= &5 / &12 ==> &0 < c1092nmpc_quartic x`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092nmpc_quartic] THEN
  C1092PRS_PROD `&0 <= (x - &7 / &24) * (&5 / &12 - x)` THEN
  C1092PRS_PROD `&0 <= ((x - &7 / &24) * (&5 / &12 - x)) * x pow 2` THEN
  C1092PRS_PROD `&0 <= ((x - &7 / &24) * (&5 / &12 - x)) * x` THEN
  C1092PRS_PROD `&0 <= (x - &7 / &24) * x pow 2` THEN
  C1092PRS_PROD `&0 <= (&5 / &12 - x) * x pow 2` THEN
  NLIN_TAC []);;

(* the half-angle form of the norm defect (identity step of last_margin) *)
let C1092NMPC_LAST_IDENTITY = prove
 (`forall c s x. (&1 + x pow 2) * c = &1 - x pow 2 /\ (&1 + x pow 2) * s = &2 * x
     ==> &1250 * (&1 + x pow 2) pow 2 *
         (&1 - c1092nmpc_P1 c s pow 2 - c1092nmpc_Q1 c s pow 2) = c1092nmpc_quartic x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c = (&1 - x pow 2) / (&1 + x pow 2) /\ s = (&2 * x) / (&1 + x pow 2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
  [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092nmpc_P1; c1092nmpc_Q1; c1092nmpc_quartic] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 < x ==> ~(x = &0)`)) THEN
  CONV_TAC REAL_FIELD);;

(* Lean: last_margin *)
let C1092NMPC_LAST_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\ &7 / &24 <= s / (&1 + c)
     ==> &0 < &1 - c1092nmpc_P1 c s * b - c1092nmpc_Q1 c s * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NMPC_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half c s <= &5 / &12` MP_TAC THENL
  [REWRITE_TAC[C1092WPS_half] THEN
   SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [C1092NMPC_LP_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN C1092NMPC_LP_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&7 / &24 <= s / (&1 + c)` THEN REWRITE_TAC[GSYM C1092WPS_half] THEN
  SPEC_TAC(`C1092WPS_half c s`,`x:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `x:real`] C1092NMPC_LAST_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` C1092NMPC_QUARTIC_POSITIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1092nmpc_P1 c s`; `c1092nmpc_Q1 c s`; `b:real`; `r:real`; `&1`]
    C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1250 * (&1 + x pow 2) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (&1250 * (&1 + x pow 2) pow 2) *
     --(&1 - c1092nmpc_P1 c s pow 2 - c1092nmpc_Q1 c s pow 2)` THEN
  C1092NMPC_LP_TAC);;

let C1092NMPC_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: transverse_margin *)
let C1092NMPC_TRANSVERSE_MARGIN = prove
 (`forall c s. c977cc_normal c s /\ &7 / &24 <= s / (&1 + c)
     ==> (&229 / &200) * c + (&61 / &1000) * s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NMPC_LP_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&7 / &24 <= s / (&1 + c)` THEN REWRITE_TAC[GSYM C1092WPS_half] THEN
  SPEC_TAC(`C1092WPS_half c s`,`x:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&336 / &625 <= s` ASSUME_TAC THENL
  [C1092PRS_PROD `&0 <= (x - &7 / &24) * (&2 - (&336 / &625) * (x + &7 / &24))` THEN
   SUBGOAL_THEN `&0 <= (&1 + x pow 2) * (s - &336 / &625)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= s - k ==> k <= s`) THEN
   MATCH_MP_TAC C1092NMPC_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + x pow 2` THEN
   ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(SPECL [`&527 / &625`; `&336 / &625`; `c:real`; `s:real`;
                `&229 / &200`; `&61 / &1000`] CCUCC_DECREASING) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
   CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;
