(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardSmallThreeBoundaryScalars.lean *)
(* (N12Compact.C1092MPPMInwardSmallThree).  Rational margins for the actual  *)
(* B--E sources in the small-inward ending.  Normal: c977cc_normal           *)
(* (normal_bounds: C977CC_NORMAL_BOUNDS); BottomAngle.relative_dot_lower:    *)
(* C1092IFBS_RELATIVE_DOT_LOWER.  The structure BoundaryRange is the         *)
(* predicate c1092isbs_range (its fields in order, conjoined).               *)
(* Tag C1092ISBS_ / c1092isbs_.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardSmallThreeBottom.ml";;

let C1092ISBS_LIN = NLIN_TAC ~deg2:false [];;
let C1092ISBS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092ISBS_LIN; ALL_TAC];;
let C1092ISBS_HAVE tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;

(* Lean: nu *)
let c1092isbs_nu = new_definition
 `c1092isbs_nu (d:real) (t:real) (h:real) (k:real) = d * h - t * k`;;

(* Lean: eta *)
let c1092isbs_eta = new_definition
 `c1092isbs_eta (d:real) (t:real) (h:real) (k:real) = t * h + d * k`;;

(* Lean: X0 *)
let c1092isbs_X0 = new_definition
 `c1092isbs_X0 (d:real) (t:real) = &1 - d - t + (&3 / &5) * d * t`;;

(* Lean: Y0 *)
let c1092isbs_Y0 = new_definition
 `c1092isbs_Y0 (d:real) (t:real) = t - d - &1 + (&3 / &5) * d pow 2`;;

(* Lean: Delta0 *)
let c1092isbs_Delta0 = new_definition
 `c1092isbs_Delta0 (d:real) (t:real) = &1 - t - (&3 / &5) * d`;;

(* Lean: Z0 *)
let c1092isbs_Z0 = new_definition
 `c1092isbs_Z0 (d:real) (t:real) (h:real) (k:real) =
    (&49 / &100) * d * h + t * (&1 - (&543 / &500) * h) -
    k * ((&49 / &100) * t + (&543 / &500) * d)`;;

(* Lean: BoundaryRange (structure: normal, cosine, sineLow, sineHigh,
   bottomCosine, bottomUnit, bottomLow, bottomHigh) *)
let c1092isbs_range = new_definition
 `c1092isbs_range (d:real) (t:real) (h:real) (k:real) <=>
    c977cc_normal d t /\ &15 / &17 < d /\ &1 / &3 < t /\ t < &8 / &17 /\
    &999 / &1000 < h /\ h pow 2 + k pow 2 = &1 /\ --(&43 / &1000) < k /\ k < &21 / &1000`;;

let C1092ISBS_RANGE_TAC =
  REWRITE_TAC[c1092isbs_range] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)) THEN
  REPEAT DISCH_TAC;;

(* Lean: boundary_coefficients *)
let C1092ISBS_BOUNDARY_COEFFICIENTS = prove
 (`forall d t h k. c1092isbs_range d t h k
     ==> &0 < c1092isbs_nu d t h k /\ c1092isbs_nu d t h k <= &1 /\
         &7 / &25 < c1092isbs_eta d t h k /\ h <= &1`,
  C1092ISBS_RANGE_TAC THEN
  C1092ISBS_HAVE `h <= &1` (NLIN_TAC [SQ_NONNEG `k:real`; SQ_NONNEG `h - &1`]) THEN
  C1092ISBS_PROD `&0 < (d - &22 / &25) * h` THEN
  C1092ISBS_PROD `&0 <= t * (&21 / &1000 - k)` THEN
  C1092ISBS_HAVE `&0 < c1092isbs_nu d t h k`
    (REWRITE_TAC[c1092isbs_nu] THEN C1092ISBS_LIN) THEN
  C1092ISBS_PROD `&0 < (t - &1 / &3) * h` THEN
  C1092ISBS_PROD `&0 < d * (k + &43 / &1000)` THEN
  C1092ISBS_HAVE `&7 / &25 < c1092isbs_eta d t h k`
    (REWRITE_TAC[c1092isbs_eta] THEN C1092ISBS_LIN) THEN
  C1092ISBS_HAVE `c1092isbs_nu d t h k pow 2 + c1092isbs_eta d t h k pow 2 = &1`
    (REWRITE_TAC[c1092isbs_nu; c1092isbs_eta] THEN
     UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `h pow 2 + k pow 2 = &1` THEN
     CONV_TAC REAL_RING) THEN
  ASM_REWRITE_TAC[] THEN
  NLIN_TAC [SQ_NONNEG `c1092isbs_eta d t h k`; SQ_NONNEG `c1092isbs_nu d t h k - &1`]);;

(* Lean: boundary_margins *)
let C1092ISBS_BOUNDARY_MARGINS = prove
 (`forall d t h k. c1092isbs_range d t h k /\ &1 < t + (&343 / &500) * d
     ==> c1092isbs_X0 d t < --(&1 / &17) /\ &0 < c1092isbs_Y0 d t + &543 / &500 /\
         c1092isbs_Y0 d t + &543 / &500 < &3 / &10 /\ &0 < c1092isbs_Delta0 d t`,
  C1092ISBS_RANGE_TAC THEN
  C1092ISBS_PROD `&0 < (d - &15 / &17) * t` THEN
  C1092ISBS_HAVE `&5 / &17 < d * t` C1092ISBS_LIN THEN
  C1092ISBS_HAVE `(&1 + d + t) * (c1092isbs_X0 d t + d * t / &5) =
                  d * t * ((&4 / &5) * (&1 + d + t) - &2)`
    (REWRITE_TAC[c1092isbs_X0] THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
     CONV_TAC REAL_RING) THEN
  C1092ISBS_PROD `&0 < (d * t) * (&2 - (&4 / &5) * (&1 + d + t))` THEN
  C1092ISBS_HAVE `d * t * ((&4 / &5) * (&1 + d + t) - &2) < &0` C1092ISBS_LIN THEN
  C1092ISBS_HAVE `c1092isbs_X0 d t + d * t / &5 < &0`
    (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
     SUBGOAL_THEN `&0 <= (&1 + d + t) * (c1092isbs_X0 d t + d * t / &5)` MP_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN C1092ISBS_LIN;
       ASM_REWRITE_TAC[] THEN C1092ISBS_LIN]) THEN
  C1092ISBS_PROD `&0 <= (&1 - d) * (&543 / &500 - (&3 / &5) * d)` THEN
  C1092ISBS_HAVE `d pow 2 <= &1` (NLIN_TAC [SQ_NONNEG `t:real`]) THEN
  C1092ISBS_PROD `&0 < (&8 / &17 - t) * (&1 - t)` THEN
  C1092ISBS_HAVE `(&1 - t) pow 2 - ((&3 / &5) * d) pow 2 = (&34 / &25) * (&8 / &17 - t) * (&1 - t)`
    (UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING) THEN
  C1092ISBS_HAVE `&0 < c1092isbs_Delta0 d t`
    (REWRITE_TAC[c1092isbs_Delta0] THEN
     NLIN_TAC [SQ_NONNEG `&1 - t - (&3 / &5) * d`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [C1092ISBS_LIN;
    REWRITE_TAC[c1092isbs_Y0] THEN C1092ISBS_LIN;
    REWRITE_TAC[c1092isbs_Y0] THEN NLIN_TAC []]);;

(* Lean: first_source_margin *)
let C1092ISBS_FIRST_SOURCE_MARGIN = prove
 (`forall d t h k. c1092isbs_range d t h k /\ &1 < t + (&343 / &500) * d
     ==> h * c1092isbs_X0 d t + k * (c1092isbs_Y0 d t + &543 / &500) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `k:real`] C1092ISBS_BOUNDARY_MARGINS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092isbs_range d t h k` THEN REWRITE_TAC[c1092isbs_range] THEN STRIP_TAC THEN
  C1092ISBS_PROD `&0 < h * --(c1092isbs_X0 d t + &1 / &17)` THEN
  C1092ISBS_PROD `&0 < (&21 / &1000 - k) * (c1092isbs_Y0 d t + &543 / &500)` THEN
  C1092ISBS_LIN);;

(* Lean: positive_transverse_coefficient *)
let C1092ISBS_POSITIVE_TRANSVERSE_COEFFICIENT = prove
 (`forall d t h k. c1092isbs_range d t h k /\ &0 <= k ==> &1 / &3 < c1092isbs_Z0 d t h k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `k:real`] C1092ISBS_BOUNDARY_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092isbs_range d t h k` THEN C1092ISBS_RANGE_TAC THEN
  C1092ISBS_PROD `&0 < (d - &22 / &25) * h` THEN
  C1092ISBS_PROD `&0 <= t * (&1 - (&543 / &500) * h + &43 / &500)` THEN
  C1092ISBS_PROD `&0 <= (&21 / &1000 - k) * ((&49 / &100) * t + (&543 / &500) * d)` THEN
  REWRITE_TAC[c1092isbs_Z0] THEN C1092ISBS_LIN);;

(* Lean: negative_transverse_margin *)
let C1092ISBS_NEGATIVE_TRANSVERSE_MARGIN = prove
 (`forall d t h k. c1092isbs_range d t h k /\ k < &0
     ==> &0 < d * (&1 - h) - (&543 / &500) * d * k pow 2 +
              (--k) * t * ((&543 / &500) * h - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `k:real`] C1092ISBS_BOUNDARY_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092isbs_range d t h k` THEN C1092ISBS_RANGE_TAC THEN
  ABBREV_TAC `l = --k` THEN
  SUBGOAL_THEN `k = --l` SUBST_ALL_TAC THENL [EXPAND_TAC "l" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_NEG; ARITH; REAL_NEG_NEG]) THEN
  REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_NEG_NEG] THEN
  C1092ISBS_HAVE `&0 < l` C1092ISBS_LIN THEN
  C1092ISBS_HAVE `l pow 2 / &2 <= &1 - h` (NLIN_TAC [SQ_NONNEG `&1 - h`]) THEN
  C1092ISBS_PROD `&0 <= d * ((&1 - h) - l pow 2 / &2)` THEN
  C1092ISBS_PROD `&0 <= (&1 - d) * (l * l)` THEN
  C1092ISBS_PROD `&0 < l * (&43 / &1000 - l)` THEN
  C1092ISBS_PROD `&0 <= (t - &1 / &3) * ((&543 / &500) * h - &1)` THEN
  C1092ISBS_HAVE `&0 <= t * ((&543 / &500) * h - &1) -
                        (&1 / &3) * ((&543 / &500) * (&999 / &1000) - &1)` C1092ISBS_LIN THEN
  C1092ISBS_PROD `&0 <= l * (t * ((&543 / &500) * h - &1) -
                        (&1 / &3) * ((&543 / &500) * (&999 / &1000) - &1))` THEN
  C1092ISBS_LIN);;

(* Lean: negative_relative_cosine *)
let C1092ISBS_NEGATIVE_RELATIVE_COSINE = prove
 (`forall d t h k. c1092isbs_range d t h k /\ k < &0 ==> d <= c1092isbs_nu d t h k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092isbs_range d t h k` THEN C1092ISBS_RANGE_TAC THEN
  C1092ISBS_HAVE `c977cc_normal h (--k)`
    (REWRITE_TAC[c977cc_normal; REAL_POW_NEG; ARITH] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN C1092ISBS_LIN) THEN
  C1092ISBS_PROD `&0 < (t - &1 / &3) * h` THEN
  C1092ISBS_PROD `&0 <= (&1 - d) * --k` THEN
  C1092ISBS_HAVE `--k * d <= h * t` C1092ISBS_LIN THEN
  MP_TAC(SPECL [`h:real`; `--k`; `d:real`; `t:real`] C1092IFBS_RELATIVE_DOT_LOWER) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092isbs_nu] THEN DISCH_TAC THEN C1092ISBS_LIN);;
