(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingPositiveBoundCoefficients.lean *)
(* (namespace N12Compact.C1092MPPMMissingPositiveBoundaries.Scalars).       *)
(* Continuous coefficient bounds for sections 5--6.  The square C is        *)
(* (c, s, u, v, a); Data / profile / central_bounds: c1092mpbp_data /       *)
(* C1092MPBP_PROFILE / C1092MPBP_CENTRAL_BOUNDS; half / quarter_data:       *)
(* C1092WPS_half / C1092WPS_QUARTER_DATA; Arc.diagonal / diagonal_data:     *)
(* c1092mpba_diagonal / C1092MPBA_DIAGONAL_DATA; cosH / sinH:               *)
(* c1092sps_cosH / c1092sps_sinH.  The scalar inequalities are proved by    *)
(* NLIN certificates on the unit circle instead of the Lean half-angle      *)
(* polynomial identities.  Tag C1092MPBC_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundArc.ml";;

(* Lean: bottomA, bottomB, leftPlusA, leftPlusB, leftMinusA, leftMinusB (definitions) *)
let c1092mpbc_bottomA = new_definition
 `c1092mpbc_bottomA (a:real) (c:real) (s:real) =
    a * ((c + s) / &2 - &1 / s) + c / s - (&11 / &25) * c pow 2`;;
let c1092mpbc_bottomB = new_definition
 `c1092mpbc_bottomB (a:real) (c:real) (s:real) = --a * s - &1 + (&11 / &25) * c * s`;;
let c1092mpbc_leftPlusA = new_definition
 `c1092mpbc_leftPlusA (a:real) (c:real) (s:real) = --a * c - &1 + c * s`;;
let c1092mpbc_leftPlusB = new_definition
 `c1092mpbc_leftPlusB (a:real) (c:real) (s:real) =
    a * ((c + s) / &2 - &1 / c) + s / c - s pow 2`;;
let c1092mpbc_leftMinusA = new_definition
 `c1092mpbc_leftMinusA (a:real) (c:real) (s:real) =
    a * (c + s) - (&3 / &10) * c pow 2 - c * s - &36 / &25`;;
let c1092mpbc_leftMinusB = new_definition
 `c1092mpbc_leftMinusB (a:real) (c:real) (s:real) =
    --a * ((&1 + s * (c + s)) / (&2 * c) + s + s pow 2 / c) + (&3 / &10) * c * s + s pow 2 +
    (&36 / &25) * s / c`;;

let C1092MPBC_LIN = REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092MPBC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   (C1092MPBC_LIN ORELSE NLIN_TAC []); ALL_TAC];;

let C1092MPBC_POS_OF_MUL = prove
 (`forall k x. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC);;

(* the central bounds, the unit relation and c, s > 0 as assumptions *)
let C1092MPBC_BOUNDS_TAC =
  FIRST_ASSUM(fun th -> if can (term_match [] `c1092mpbp_data c s u v a`) (concl th) then
    MP_TAC(MATCH_MP C1092MPBP_CENTRAL_BOUNDS
      (CONJ (ASSUME `c * c + s * s = &1`) (CONJ (ASSUME `&1 < a`) th))) else NO_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c /\ &0 < s` STRIP_ASSUME_TAC THENL [C1092MPBC_LIN; ALL_TAC];;

(* Lean: half_specs *)
let C1092MPBC_HALF_SPECS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a
     ==> &0 < C1092WPS_half c s /\ C1092WPS_half c s < &1 / &2 /\
         C1092WPS_half c s <= c1092mpba_diagonal /\
         c = c1092sps_cosH (C1092WPS_half c s) /\ s = c1092sps_sinH (C1092WPS_half c s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092mpbp_profile] THEN STRIP_TAC THEN
  C1092MPBC_BOUNDS_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN C1092MPBC_LIN; ALL_TAC] THEN
  UNDISCH_TAC `&13 / &87 < C1092WPS_half c s` THEN
  UNDISCH_TAC `C1092WPS_half c s < &1 / &2` THEN
  SPEC_TAC(`C1092WPS_half c s`, `q:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [C1092MPBC_LIN;
    MP_TAC C1092MPBA_DIAGONAL_DATA THEN
    SPEC_TAC(`c1092mpba_diagonal`, `dg:real`) THEN GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    SUBGOAL_THEN `q * q + &2 * q <= &1` ASSUME_TAC THENL
     [C1092MPBC_PROD `&0 <= (&1 + q * q) * (c - s)` THEN C1092MPBC_LIN; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPBC_PROD `&0 < (q - dg) * (q + dg + &2)` THEN C1092MPBC_LIN;
    REWRITE_TAC[c1092sps_cosH] THEN
    MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[c1092sps_sinH] THEN
    MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
    ASM_REAL_ARITH_TAC]);;

(* Lean: bottom_coefficients *)
let C1092MPBC_BOTTOM_COEFFICIENTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ a <= &1001 / &1000 /\ c1092mpbp_data c s u v a
     ==> &3 / &100 < c1092mpbc_bottomA a c s /\
         c1092mpbc_bottomB a c s < --(&1453 / &1250)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBC_BOUNDS_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `s * c1092mpbc_bottomA a c s =
                  a * (s * (c + s) / &2 - &1) + c - (&11 / &25) * (c * c) * s`
      ASSUME_TAC THENL
     [REWRITE_TAC[c1092mpbc_bottomA] THEN
      SUBGOAL_THEN `~(s = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s * (c + s) / &2 - &1 + c - (&11 / &25) * (c * c) * s - s / &25`
      ASSUME_TAC THENL
     [NLIN_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c - &1`; SQ_NONNEG `c + s - &1`]; ALL_TAC] THEN
    C1092MPBC_PROD `&0 <= (a - &1) * (s * (c + s) / &2)` THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x < y <=> &0 < y - x`] THEN
    MATCH_MP_TAC C1092MPBC_POS_OF_MUL THEN EXISTS_TAC `s:real` THEN
    ASM_REWRITE_TAC[] THEN C1092MPBC_LIN;
    REWRITE_TAC[c1092mpbc_bottomB] THEN
    C1092MPBC_PROD `&0 < s * (a - &1)` THEN
    C1092MPBC_PROD `&0 <= s * (&1 - c)` THEN
    C1092MPBC_LIN]);;

(* Lean: left_plus_coefficient *)
let C1092MPBC_LEFT_PLUS_COEFFICIENT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ a <= &1001 / &1000 /\ c1092mpbp_data c s u v a
     ==> --(&11 / &50) < c1092mpbc_leftPlusB a c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBC_BOUNDS_TAC THEN
  SUBGOAL_THEN `c * c1092mpbc_leftPlusB a c s =
                a * (c * (c + s) / &2 - &1) + s - (s * s) * c` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpbc_leftPlusB] THEN
    SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &1000 < c * (c + s) / &2 - &1 + s - (s * s) * c + (&11 / &50) * c`
    ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  C1092MPBC_PROD `&0 <= (a - &1) * (c * (c + s) / &2)` THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x < y <=> &0 < y - x`] THEN
  MATCH_MP_TAC C1092MPBC_POS_OF_MUL THEN EXISTS_TAC `c:real` THEN
  ASM_REWRITE_TAC[] THEN C1092MPBC_LIN);;

(* Lean: left_minus_at_one (private) *)
let C1092MPBC_LEFT_MINUS_AT_ONE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a
     ==> --(&3 / &4) < c1092mpbc_leftMinusA (&1) c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBC_BOUNDS_TAC THEN
  REWRITE_TAC[c1092mpbc_leftMinusA; REAL_POW_2] THEN
  NLIN_TAC [SQ_NONNEG `c - s`]);;

(* Lean: left_minus_coefficients *)
let C1092MPBC_LEFT_MINUS_COEFFICIENTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a
     ==> --(&3 / &4) < c1092mpbc_leftMinusA a c s /\
         c1092mpbc_leftMinusB a c s < --(&23 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBC_LEFT_MINUS_AT_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MPBC_BOUNDS_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `--(&3 / &4) < c1092mpbc_leftMinusA (&1) c s` THEN
    REWRITE_TAC[c1092mpbc_leftMinusA] THEN DISCH_TAC THEN
    C1092MPBC_PROD `&0 < (a - &1) * (c + s)` THEN C1092MPBC_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * c1092mpbc_leftMinusB a c s =
                --a * ((&1 + s * (c + s)) / &2 + s * c + s * s) + (&3 / &10) * (c * c) * s +
                (s * s) * c + (&36 / &25) * s` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpbc_leftMinusB] THEN
    SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&1 + s * (c + s)) / &2 - s * c - s * s + (&3 / &10) * (c * c) * s +
                (s * s) * c + (&36 / &25) * s + (&23 / &50) * c < &0` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - s`]; ALL_TAC] THEN
  C1092MPBC_PROD `&0 <= (a - &1) * ((&1 + s * (c + s)) / &2 + s * c + s * s)` THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x < y <=> &0 < y - x`] THEN
  MATCH_MP_TAC C1092MPBC_POS_OF_MUL THEN EXISTS_TAC `c:real` THEN
  ASM_REWRITE_TAC[] THEN C1092MPBC_LIN);;
