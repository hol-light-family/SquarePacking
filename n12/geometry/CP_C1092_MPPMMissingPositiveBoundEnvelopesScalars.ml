(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingPositiveBoundEnvelopesScalars  *)
(* .lean (namespace                                                          *)
(* N12Compact.C1092MPPMMissingPositiveBoundaries.Envelopes).  Continuous     *)
(* northwest boundary margins.  The square C is (c, s, u, v, a) with the     *)
(* hypotheses c * c + s * s = &1 (unit normal), &1 < a (side) and            *)
(* c1092mpbp_data c s u v a (Data C).  profile / central_bounds:             *)
(* C1092MPBP_PROFILE / C1092MPBP_CENTRAL_BOUNDS; half / quarter_data:        *)
(* C1092WPS_half / C1092WPS_QUARTER_DATA; cosH / sinH: c1092sps_cosH /       *)
(* c1092sps_sinH; Arc.value / nonneg / diagonal / diagonal_data:             *)
(* c1092mpba_value / C1092MPBA_NONNEG / c1092mpba_diagonal /                 *)
(* C1092MPBA_DIAGONAL_DATA; half_specs, bottomA .. leftMinusB and the        *)
(* coefficient bounds: C1092MPBC_*; b / ell / arc (ShallowCentralScalars):   *)
(* c1092scs_b / c1092scs_ell / C1092SCS_ARC.  Real.sqrt is sqrt.  The        *)
(* identities `aligned` and `margins` are proved on the unit circle with     *)
(* REAL_FIELD instead of the Lean half-angle substitution.  Tag C1092MPBES_. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundCoefficients.ml";;
needs "n12/geometry/CP_C1092_ShallowBoundarySupport.ml";;

let C1092MPBES_LIN = REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092MPBES_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   (C1092MPBES_LIN ORELSE NLIN_TAC []); ALL_TAC];;

(* x <= y from &0 < k and k * x <= k * y *)
let C1092MPBES_CANCEL = prove
 (`forall k x y. &0 < k /\ k * x <= k * y ==> x <= y`,
  MESON_TAC[REAL_LE_LMUL_EQ]);;

(* the profile, central and normal bounds of a Data square *)
let C1092MPBES_FACTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a
     ==> (--c - s <= u /\ u + a <= --(&13 / &50) * c /\
          (&14 / &25) * s - c <= v /\ v + a <= s /\ &0 < s /\
          a <= (&37 / &50) * c + s /\ a <= c + (&11 / &25) * s /\
          &13 / &87 < C1092WPS_half c s /\ C1092WPS_half c s < &1 / &2) /\
         (&7 / &10 < c /\ &29 / &100 < s /\ s < &71 / &100 /\ c * s <= &1 / &2 /\
          &156 / &125 < c + s /\ &0 <= c - s /\ c - s < &133 / &200 /\
          (&61 / &200) * c < s /\ c < &3700 / &3869 /\ &1131 / &3869 < s) /\
         c977cc_normal c s /\ &0 < c /\ c <= &1 /\ s <= c /\ &0 <= s /\
         c pow 2 + s pow 2 = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBP_PROFILE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBP_CENTRAL_BOUNDS) THEN
  ASM_REWRITE_TAC[c1092mpbp_profile] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mpbp_data] (ASSUME `c1092mpbp_data c s u v a`)) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal c s`)) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

let C1092MPBES_SETUP_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBES_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* Lean: bottomValue, leftValue, bottomPlusA, bottomPlusB (definitions) *)
let c1092mpbes_bottomValue = new_definition
 `c1092mpbes_bottomValue (a:real) (A:real) (B:real) (h:real) (t:real) =
    (a / &2) * (&1 + t pow 2 + h * t) + A * h + B * t`;;

let c1092mpbes_leftValue = new_definition
 `c1092mpbes_leftValue (a:real) (A:real) (B:real) (h:real) (t:real) =
    (a / &2) * (&1 + h pow 2 + h * t) + A * h + B * t`;;

let c1092mpbes_bottomPlusA = new_definition
 `c1092mpbes_bottomPlusA (a:real) (c:real) (s:real) =
    --a * (&3 / &2 + c * (c + s) / &2) / s + a * (s - c) + c * (&2 / s + (&37 / &50) * c)`;;

let c1092mpbes_bottomPlusB = new_definition
 `c1092mpbes_bottomPlusB (a:real) (c:real) (s:real) =
    a * (c + s) - &2 - (&37 / &50) * c * s`;;

(* Lean: diagonal_bounds *)
let C1092MPBES_DIAGONAL_BOUNDS = prove
 (`&7 / &5 < sqrt(&2) /\ sqrt(&2) < &3 / &2 /\ sqrt(&2) pow 2 = &2`,
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) pow 2 = &2` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_ARITH `&0 < &2 /\ &0 <= &2`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN NLIN_TAC []);;

(* Lean: circle_data *)
let C1092MPBES_CIRCLE_DATA = prove
 (`forall h t. &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1
     ==> &0 <= C1092WPS_half t h /\ C1092WPS_half t h <= &1 /\
         t = c1092sps_cosH (C1092WPS_half t h) /\ h = c1092sps_sinH (C1092WPS_half t h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:real`; `h:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half t h`,`q:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; C1092SPS_HALF_DEN_POS] THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: half_mono *)
let C1092MPBES_HALF_MONO = prove
 (`forall h t h1 t1. &0 <= h /\ &0 <= t /\ h <= h1 /\ t1 <= t /\ &0 <= t1
     ==> C1092WPS_half t h <= C1092WPS_half t1 h1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092WPS_half] THEN
  SUBGOAL_THEN `h1 / (&1 + t1) - h / (&1 + t) =
                (h1 * (&1 + t) - h * (&1 + t1)) / ((&1 + t1) * (&1 + t))` MP_TAC THENL
   [SUBGOAL_THEN `~(&1 + t1 = &0) /\ ~(&1 + t = &0)` MP_TAC THENL
     [RASM_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (h1 * (&1 + t) - h * (&1 + t1)) / ((&1 + t1) * (&1 + t))`
    MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [C1092MPBES_PROD `&0 <= h * (t - t1)` THEN
    C1092MPBES_PROD `&0 <= (h1 - h) * (&1 + t)` THEN RASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC]);;

(* Lean: circle_order *)
let C1092MPBES_CIRCLE_ORDER = prove
 (`forall c s h t. &0 < c /\ &0 < s /\ &0 <= h /\ &0 <= t /\
             c pow 2 + s pow 2 = &1 /\ h pow 2 + t pow 2 = &1 /\ &0 <= s * t - c * h
     ==> h <= s /\ c <= t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `h <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `t < c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092MPBES_PROD `&0 < (h - s) * (h + s)` THEN
      C1092MPBES_PROD `&0 <= (t - c) * (t + c)` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
    C1092MPBES_PROD `&0 < c * (h - s)` THEN
    C1092MPBES_PROD `&0 < s * (c - t)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092MPBES_PROD `&0 < (c - t) * (c + t)` THEN
  C1092MPBES_PROD `&0 <= (s - h) * (s + h)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC);;

(* Lean: circle_order_reverse *)
let C1092MPBES_CIRCLE_ORDER_REVERSE = prove
 (`forall c s h t. &0 < c /\ &0 < s /\ &0 <= h /\ &0 <= t /\
             c pow 2 + s pow 2 = &1 /\ h pow 2 + t pow 2 = &1 /\ s * t - c * h <= &0
     ==> s <= h /\ t <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `h < s` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092MPBES_PROD `&0 < (t - c) * (t + c)` THEN
      C1092MPBES_PROD `&0 <= (h - s) * (h + s)` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
    C1092MPBES_PROD `&0 < c * (s - h)` THEN
    C1092MPBES_PROD `&0 < s * (t - c)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092MPBES_PROD `&0 < (s - h) * (s + h)` THEN
  C1092MPBES_PROD `&0 <= (c - t) * (c + t)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC);;

(* Lean: bottom_difference *)
let C1092MPBES_BOTTOM_DIFFERENCE = prove
 (`forall a A B h t h1 t1. h pow 2 + t pow 2 = h1 pow 2 + t1 pow 2
     ==> ((h + h1) / &2) *
         (c1092mpbes_bottomValue a A B h t - c1092mpbes_bottomValue a A B h1 t1) =
         (t - t1) * (a * (((h + h1) / &2) * ((t + t1) / &2) +
           (((h + h1) / &2) pow 2 - ((t + t1) / &2) pow 2) / &2) -
           A * ((t + t1) / &2) + B * ((h + h1) / &2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mpbes_bottomValue] THEN CONV_TAC REAL_RING);;

(* Lean: left_difference *)
let C1092MPBES_LEFT_DIFFERENCE = prove
 (`forall a A B h t h1 t1. h pow 2 + t pow 2 = h1 pow 2 + t1 pow 2
     ==> ((h + h1) / &2) *
         (c1092mpbes_leftValue a A B h t - c1092mpbes_leftValue a A B h1 t1) =
         (t - t1) * (a * (--((h + h1) / &2) * ((t + t1) / &2) +
           (((h + h1) / &2) pow 2 - ((t + t1) / &2) pow 2) / &2) -
           A * ((t + t1) / &2) + B * ((h + h1) / &2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mpbes_leftValue] THEN CONV_TAC REAL_RING);;

(* Lean: aligned *)
let C1092MPBES_ALIGNED = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a
     ==> c1092mpbes_bottomValue a (c1092mpbes_bottomPlusA a c s)
           (c1092mpbes_bottomPlusB a c s) s c = &0 /\
         c1092mpbes_bottomValue a (c1092mpbc_bottomA a c s)
           (c1092mpbc_bottomB a c s) s c = &0 /\
         c1092mpbes_leftValue a (c1092mpbc_leftPlusA a c s)
           (c1092mpbc_leftPlusB a c s) s c = &0 /\
         c1092mpbes_leftValue a (c1092mpbc_leftMinusA a c s)
           (c1092mpbc_leftMinusB a c s) s c = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBES_SETUP_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(s = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN
  REWRITE_TAC[c1092mpbes_bottomValue; c1092mpbes_leftValue; c1092mpbes_bottomPlusA;
    c1092mpbes_bottomPlusB; c1092mpbc_bottomA; c1092mpbc_bottomB; c1092mpbc_leftPlusA;
    c1092mpbc_leftPlusB; c1092mpbc_leftMinusA; c1092mpbc_leftMinusB] THEN
  CONV_TAC REAL_FIELD);;

(* Arc.value is bottomValue at (sinH z, cosH z) *)
let C1092MPBES_ARC_VALUE = prove
 (`forall a A B z. c1092mpba_value a A B z =
             c1092mpbes_bottomValue a A B (c1092sps_sinH z) (c1092sps_cosH z)`,
  REWRITE_TAC[c1092mpba_value; c1092mpbes_bottomValue]);;

let C1092MPBES_POS_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC);;

(* Lean: bottom_diagonal *)
let C1092MPBES_BOTTOM_DIAGONAL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a
     ==> &0 <= c1092mpbes_bottomValue a (c1092mpbc_bottomA a c s) (c1092mpbc_bottomB a c s)
                (sqrt(&2) / &2) (sqrt(&2) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBES_SETUP_TAC THEN
  MP_TAC C1092MPBES_DIAGONAL_BOUNDS THEN
  SPEC_TAC(`sqrt(&2)`,`r:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c + s <= r` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPBES_PROD `&0 < (c + s - r) * (c + s + r)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * s - &1 + s * (c - s) / &2 <= &0` ASSUME_TAC THENL
   [C1092MPBES_PROD `&0 <= (r / &2) * (r - (c + s))` THEN
    C1092MPBES_PROD `&0 <= (c - s) * (r - s)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * (r - (c + s)) <= (&3 / &5) * (c - s) pow 2` ASSUME_TAC THENL
   [C1092MPBES_PROD `&0 <= (r - (c + s)) * ((&3 / &5) * (r + (c + s)) - r)` THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD
   `&0 <= (c - s) * ((&7 / &25) * r + (&7 / &50) * (c + s) - (&64 / &125) * (c - s))` THEN
  SUBGOAL_THEN `&0 <= r * (c + (&11 / &25) * s) - &36 / &25 + (&3 / &50) * c pow 2 +
                      (&4 / &25) * c * s - (&11 / &50) * s pow 2` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(s * r) * c1092mpbes_bottomValue a (c1092mpbc_bottomA a c s) (c1092mpbc_bottomB a c s)
                (r / &2) (r / &2) =
    a * (r * s - &1 + s * (c - s) / &2) + (c - s) * (&1 - (&11 / &25) * c * s)`
  ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpbes_bottomValue; c1092mpbc_bottomA; c1092mpbc_bottomB] THEN
    SUBGOAL_THEN `~(s = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `r pow 2 = &2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  C1092MPBES_PROD `&0 <= (c + (&11 / &25) * s - a) * --(r * s - &1 + s * (c - s) / &2)` THEN
  C1092MPBES_PROD `&0 <= s * (r * (c + (&11 / &25) * s) - &36 / &25 + (&3 / &50) * c pow 2 +
                      (&4 / &25) * c * s - (&11 / &50) * s pow 2)` THEN
  MATCH_MP_TAC C1092MPBES_POS_CANCEL THEN EXISTS_TAC `s * r` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: bottom_minus_low *)
let C1092MPBES_BOTTOM_MINUS_LOW = prove
 (`forall c s u v a h t. c * c + s * s = &1 /\ &1 < a /\ a <= &1001 / &1000 /\
     c1092mpbp_data c s u v a /\
     &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1 /\ t <= h
     ==> &0 <= c1092mpbes_bottomValue a (c1092mpbc_bottomA a c s) (c1092mpbc_bottomB a c s) h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092MPBC_BOTTOM_COEFFICIENTS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092MPBES_BOTTOM_DIAGONAL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) / &2 /\ sqrt(&2) / &2 < &3 / &4 /\
                (sqrt(&2) / &2) pow 2 + (sqrt(&2) / &2) pow 2 = &1` MP_TAC THENL
   [MP_TAC C1092MPBES_DIAGONAL_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`sqrt(&2) / &2`,`R:real`) THEN GEN_TAC THEN
  SPEC_TAC(`c1092mpbc_bottomA a c s`,`A:real`) THEN GEN_TAC THEN
  SPEC_TAC(`c1092mpbc_bottomB a c s`,`B:real`) THEN GEN_TAC THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t <= R` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPBES_PROD `&0 < (t - R) * (t + R)` THEN
    C1092MPBES_PROD `&0 <= (h - t) * (h + t)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h + t <= &3 / &2` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `h - t:real`]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `A:real`; `B:real`; `h:real`; `t:real`; `R:real`; `R:real`]
    C1092MPBES_BOTTOM_DIFFERENCE) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < (h + R) / &2 /\ &0 <= (t + R) / &2 /\
                (t + R) / &2 + ((h + R) / &2) / &2 <= &9 / &8 /\ t - R <= &0`
    STRIP_ASSUME_TAC THENL [C1092MPBES_LIN; ALL_TAC] THEN
  ABBREV_TAC `H = (h + R) / &2` THEN ABBREV_TAC `TT = (t + R) / &2` THEN
  C1092MPBES_PROD `&0 <= a * (&9 / &8 - (TT + H / &2))` THEN
  SUBGOAL_THEN `a * (TT + H / &2) + B < &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD `&0 < H * --(a * (TT + H / &2) + B)` THEN
  C1092MPBES_PROD `&0 <= A * TT` THEN
  C1092MPBES_PROD `&0 <= a * TT pow 2` THEN
  SUBGOAL_THEN `a * (H * TT + (H pow 2 - TT pow 2) / &2) - A * TT + B * H < &0`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD `&0 <= --(t - R) *
     --(a * (H * TT + (H pow 2 - TT pow 2) / &2) - A * TT + B * H)` THEN
  SUBGOAL_THEN `&0 <= H * (c1092mpbes_bottomValue a A B h t - c1092mpbes_bottomValue a A B R R)`
    MP_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`H:real`; `c1092mpbes_bottomValue a A B h t - c1092mpbes_bottomValue a A B R R`]
    C1092MPBES_POS_CANCEL) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: bottom_plus *)
let C1092MPBES_BOTTOM_PLUS = prove
 (`forall c s u v a h t. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a /\
     &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1 /\ &0 <= s * t - c * h
     ==> &0 <= c1092mpbes_bottomValue a (c1092mpbes_bottomPlusA a c s)
                (c1092mpbes_bottomPlusB a c s) h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBES_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `t:real`] C1092MPBES_CIRCLE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBC_HALF_SPECS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o ONCE_REWRITE_RULE[EQ_SYM_EQ]) THEN
  MP_TAC(SPECL [`h:real`; `t:real`] C1092MPBES_CIRCLE_DATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o ONCE_REWRITE_RULE[EQ_SYM_EQ]) THEN
  MP_TAC(SPECL [`h:real`; `t:real`; `s:real`; `c:real`] C1092MPBES_HALF_MONO) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SCS_ARC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC C1092MPBA_DIAGONAL_DATA THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c1092mpba_value a (c1092mpbes_bottomPlusA a c s)
                     (c1092mpbes_bottomPlusB a c s) (&0)` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpba_value; c1092sps_cosH; c1092sps_sinH; c1092mpbes_bottomPlusB] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    C1092MPBES_PROD `&0 < c * s` THEN
    C1092MPBES_PROD `&0 < (a - &1) * (&1 + c + s)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092mpba_value a (c1092mpbes_bottomPlusA a c s)
                     (c1092mpbes_bottomPlusB a c s) (C1092WPS_half c s)` ASSUME_TAC THENL
   [REWRITE_TAC[C1092MPBES_ARC_VALUE] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBES_ALIGNED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c1092mpba_diagonal`; `a:real`; `c1092mpbes_bottomPlusA a c s`;
    `c1092mpbes_bottomPlusB a c s`; `&0`; `C1092WPS_half t h`; `C1092WPS_half c s`]
    C1092MPBA_NONNEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[C1092MPBES_ARC_VALUE] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: bottom_minus *)
let C1092MPBES_BOTTOM_MINUS = prove
 (`forall c s u v a h t. c * c + s * s = &1 /\ &1 < a /\ a <= &1001 / &1000 /\
     c1092mpbp_data c s u v a /\
     &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1 /\ s * t - c * h <= &0
     ==> &0 <= c1092mpbes_bottomValue a (c1092mpbc_bottomA a c s) (c1092mpbc_bottomB a c s) h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t <= h` THENL
   [MATCH_MP_TAC C1092MPBES_BOTTOM_MINUS_LOW THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `v:real`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092MPBES_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `t:real`] C1092MPBES_CIRCLE_ORDER_REVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBC_HALF_SPECS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o ONCE_REWRITE_RULE[EQ_SYM_EQ]) THEN
  MP_TAC(SPECL [`h:real`; `t:real`] C1092MPBES_CIRCLE_DATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o ONCE_REWRITE_RULE[EQ_SYM_EQ]) THEN
  MP_TAC(SPECL [`s:real`; `c:real`; `h:real`; `t:real`] C1092MPBES_HALF_MONO) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC C1092MPBA_DIAGONAL_DATA THEN STRIP_TAC THEN
  SUBGOAL_THEN `C1092WPS_half t h <= c1092mpba_diagonal` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t:real`; `h:real`] C1092WPS_QUARTER_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c1092mpba_diagonal pow 2 + &2 * c1092mpba_diagonal = &1` THEN
    UNDISCH_TAC `&0 < c1092mpba_diagonal` THEN
    UNDISCH_TAC `~(t <= h)` THEN
    UNDISCH_TAC `&0 <= h` THEN UNDISCH_TAC `&0 <= t` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`C1092WPS_half t h`,`w:real`) THEN
    SPEC_TAC(`c1092mpba_diagonal`,`d:real`) THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[REAL_NOT_LE] THEN REPEAT STRIP_TAC THEN
    C1092MPBES_PROD `&0 <= (&1 + w pow 2) * (t - h)` THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPBES_PROD `&0 < (w - d) * (w + d + &2)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092MPBES_BOTTOM_DIAGONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= c1092mpba_value a (c1092mpbc_bottomA a c s)
                     (c1092mpbc_bottomB a c s) (C1092WPS_half c s)` ASSUME_TAC THENL
   [REWRITE_TAC[C1092MPBES_ARC_VALUE] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBES_ALIGNED) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092mpba_value a (c1092mpbc_bottomA a c s)
                     (c1092mpbc_bottomB a c s) c1092mpba_diagonal` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[C1092MPBES_ARC_VALUE]; ALL_TAC] THEN
  MP_TAC(SPECL [`c1092mpba_diagonal`; `a:real`; `c1092mpbc_bottomA a c s`;
    `c1092mpbc_bottomB a c s`; `C1092WPS_half c s`; `C1092WPS_half t h`;
    `c1092mpba_diagonal`] C1092MPBA_NONNEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[C1092MPBES_ARC_VALUE] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: left_plus *)
let C1092MPBES_LEFT_PLUS = prove
 (`forall c s u v a h t. c * c + s * s = &1 /\ &1 < a /\ a <= &1001 / &1000 /\
     c1092mpbp_data c s u v a /\
     &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1 /\ &0 <= s * t - c * h
     ==> &0 <= c1092mpbes_leftValue a (c1092mpbc_leftPlusA a c s)
                (c1092mpbc_leftPlusB a c s) h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBES_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `t:real`] C1092MPBES_CIRCLE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092MPBC_LEFT_PLUS_COEFFICIENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBES_ALIGNED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `c1092mpbc_leftPlusA a c s`; `c1092mpbc_leftPlusB a c s`;
    `h:real`; `t:real`; `s:real`; `c:real`] C1092MPBES_LEFT_DIFFERENCE) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  C1092MPBES_PROD `&0 <= (s - h) * (t + c - s - h)` THEN
  SUBGOAL_THEN `h + t <= c + s` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (t + c) * (c + s - h - t)` MP_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MP_TAC(SPECL [`t + c`; `c + s - h - t`] C1092MPBES_POS_CANCEL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (h + s) / &2 /\ &7 / &10 < (t + c) / &2 /\
                --(&9 / &25) < c - (h + s) / &2 - ((t + c) / &2) / &2` STRIP_ASSUME_TAC THENL
   [C1092MPBES_LIN; ALL_TAC] THEN
  ABBREV_TAC `H = (h + s) / &2` THEN ABBREV_TAC `TT = (t + c) / &2` THEN
  ABBREV_TAC `B = c1092mpbc_leftPlusB a c s` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mpbc_leftPlusA]) THEN REWRITE_TAC[c1092mpbc_leftPlusA] THEN
  C1092MPBES_PROD `&0 < a * (c - H - TT / &2 + &9 / &25)` THEN
  SUBGOAL_THEN `&13 / &100 < a * (c - H - TT / &2) + &1 - c * s` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD `&0 < TT * (a * (c - H - TT / &2) + &1 - c * s - &13 / &100)` THEN
  C1092MPBES_PROD `&0 < H * (B + &11 / &50)` THEN
  C1092MPBES_PROD `&0 <= (a - &1) * H pow 2` THEN
  MP_TAC(SPEC `H - &11 / &50` REAL_LE_POW_2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < a * (--H * TT + (H pow 2 - TT pow 2) / &2) -
                     (--a * c - &1 + c * s) * TT + B * H` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD `&0 <= (t - c) * (a * (--H * TT + (H pow 2 - TT pow 2) / &2) -
                     (--a * c - &1 + c * s) * TT + B * H)` THEN
  MATCH_MP_TAC C1092MPBES_POS_CANCEL THEN EXISTS_TAC `H:real` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      can (term_match [] `H * (x - y:real)`) (lhs(concl th)) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: left_minus_high *)
let C1092MPBES_LEFT_MINUS_HIGH = prove
 (`forall c s u v a h t. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a /\
     &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1 /\ s * t - c * h <= &0 /\ h <= t
     ==> &0 <= c1092mpbes_leftValue a (c1092mpbc_leftMinusA a c s)
                (c1092mpbc_leftMinusB a c s) h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBES_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `t:real`] C1092MPBES_CIRCLE_ORDER_REVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092MPBC_LEFT_MINUS_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBES_ALIGNED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `c1092mpbc_leftMinusA a c s`; `c1092mpbc_leftMinusB a c s`;
    `h:real`; `t:real`; `s:real`; `c:real`] C1092MPBES_LEFT_DIFFERENCE) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  C1092MPBES_PROD `&0 <= (c - t) * (c + t - h - s)` THEN
  SUBGOAL_THEN `c + s <= h + t` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (h + s) * (h + t - c - s)` MP_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MP_TAC(SPECL [`h + s`; `h + t - c - s`] C1092MPBES_POS_CANCEL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (h + s) / &2 /\ &0 < (t + c) / &2 /\ (h + s) / &2 <= (t + c) / &2 /\
                &156 / &125 < (h + s) / &2 + (t + c) / &2 /\
                (&61 / &200) * ((t + c) / &2) < (h + s) / &2` STRIP_ASSUME_TAC THENL
   [C1092MPBES_LIN; ALL_TAC] THEN
  ABBREV_TAC `H = (h + s) / &2` THEN ABBREV_TAC `TT = (t + c) / &2` THEN
  ABBREV_TAC `A = c1092mpbc_leftMinusA a c s` THEN
  ABBREV_TAC `B = c1092mpbc_leftMinusB a c s` THEN
  SUBGOAL_THEN `--H * TT + (H pow 2 - TT pow 2) / &2 <= &0` ASSUME_TAC THENL
   [C1092MPBES_PROD `&0 <= (TT - H) * (H + TT)` THEN
    C1092MPBES_PROD `&0 <= H * TT` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD `&0 <= (a - &1) * --(--H * TT + (H pow 2 - TT pow 2) / &2)` THEN
  C1092MPBES_PROD `&0 < TT * (A + &3 / &4)` THEN
  C1092MPBES_PROD `&0 < H * (--(&23 / &50) - B)` THEN
  C1092MPBES_PROD `&0 <= H * (TT - H)` THEN
  C1092MPBES_PROD `&0 < TT * (H + TT - &156 / &125)` THEN
  SUBGOAL_THEN `a * (--H * TT + (H pow 2 - TT pow 2) / &2) - A * TT + B * H < &0`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD `&0 <= (c - t) *
     --(a * (--H * TT + (H pow 2 - TT pow 2) / &2) - A * TT + B * H)` THEN
  MATCH_MP_TAC C1092MPBES_POS_CANCEL THEN EXISTS_TAC `H:real` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      can (term_match [] `H * (x - y:real)`) (lhs(concl th)) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN RASM_ARITH_TAC);;

(* Lean: left_minus_low *)
let C1092MPBES_LEFT_MINUS_LOW = prove
 (`forall c s u v a h t. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a /\
     &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1 /\ t <= h
     ==> &0 <= c1092mpbes_leftValue a (c1092mpbc_leftMinusA a c s)
                (c1092mpbc_leftMinusB a c s) h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBES_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
    `sqrt(&2) / &2`; `sqrt(&2) / &2`] C1092MPBES_LEFT_MINUS_HIGH) THEN
  MP_TAC C1092MPBES_DIAGONAL_BOUNDS THEN STRIP_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    C1092MPBES_PROD `&0 <= (c - s) * (sqrt(&2) / &2)` THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092MPBC_LEFT_MINUS_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `A = c1092mpbc_leftMinusA a c s` THEN
  ABBREV_TAC `B = c1092mpbc_leftMinusB a c s` THEN
  SUBGOAL_THEN `sqrt(&2) * c1092mpbes_leftValue a A B (sqrt(&2) / &2) (sqrt(&2) / &2) =
                a * sqrt(&2) + A + B` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpbes_leftValue] THEN UNDISCH_TAC `sqrt(&2) pow 2 = &2` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MPBES_PROD `&0 <= sqrt(&2) * c1092mpbes_leftValue a A B (sqrt(&2) / &2) (sqrt(&2) / &2)` THEN
  SUBGOAL_THEN `&0 <= a * sqrt(&2) + A + B` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD `&0 <= (A + (&3 / &4) * a) * (h - t)` THEN
  C1092MPBES_PROD `&0 <= t * (a * sqrt(&2) + A + B)` THEN
  C1092MPBES_PROD `&0 <= h * t` THEN
  SUBGOAL_THEN `&1 <= h + t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPBES_PROD `&0 < (&1 - (h + t)) * (&1 + h + t)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD `&0 <= (h - t) * ((h + t) / &4 + sqrt(&2) / &2 - &3 / &4)` THEN
  MP_TAC(SPEC `sqrt(&2) - h - t` REAL_LE_POW_2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + h pow 2 + h * t) / &2 - sqrt(&2) * t - (&3 / &4) * (h - t)`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD `&0 <= a * ((&1 + h pow 2 + h * t) / &2 - sqrt(&2) * t - (&3 / &4) * (h - t))` THEN
  REWRITE_TAC[c1092mpbes_leftValue] THEN RASM_ARITH_TAC);;

(* Lean: left_minus *)
let C1092MPBES_LEFT_MINUS = prove
 (`forall c s u v a h t. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a /\
     &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1 /\ s * t - c * h <= &0
     ==> &0 <= c1092mpbes_leftValue a (c1092mpbc_leftMinusA a c s)
                (c1092mpbc_leftMinusB a c s) h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `h <= t` THENL
   [MATCH_MP_TAC C1092MPBES_LEFT_MINUS_HIGH THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `v:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092MPBES_LEFT_MINUS_LOW THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `v:real`] THEN ASM_REWRITE_TAC[] THEN
    RASM_ARITH_TAC]);;

(* Lean: bottomGap, leftGap (definitions) *)
let c1092mpbes_bottomGap = new_definition
 `c1092mpbes_bottomGap (a:real) (c:real) (s:real) (J:real) (K:real) (h:real) (t:real) =
    --h * c1092scs_b a c s K - &2 * t + (a / &2) * (&1 + t pow 2 + h * t) -
    ((s * t - c * h) * J + (s * h + c * t) * (K - a) - a * max (s * t - c * h) (&0))`;;

let c1092mpbes_leftGap = new_definition
 `c1092mpbes_leftGap (a:real) (c:real) (s:real) (J:real) (K:real) (h:real) (t:real) =
    (s * t - c * h) * J + (s * h + c * t) * K + a * max (c * h - s * t) (&0) -
    (&2 * h + t * c1092scs_ell a c s K - (a / &2) * (&1 + h pow 2 + h * t))`;;

let C1092MPBES_PROD1 tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC];;

(* Lean: margins *)
let C1092MPBES_MARGINS = prove
 (`forall c s u v a h t. c * c + s * s = &1 /\ &1 < a /\ a <= &1001 / &1000 /\
     c1092mpbp_data c s u v a /\ &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1
     ==> &0 <= c1092mpbes_bottomGap a c s (u + a) (v + a) h t /\
         &0 <= c1092mpbes_leftGap a c s (u + a) (v + a) h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBES_SETUP_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(s = &0)` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s * t - c * h` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`; `t:real`]
      C1092MPBES_BOTTOM_PLUS) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`; `t:real`]
      C1092MPBES_LEFT_PLUS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `max (s * t - c * h) (&0) = s * t - c * h /\ max (c * h - s * t) (&0) = &0`
      STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[real_max] THEN CONJ_TAC THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `c1092mpbes_bottomGap a c s (u + a) (v + a) h t =
      c1092mpbes_bottomValue a (c1092mpbes_bottomPlusA a c s) (c1092mpbes_bottomPlusB a c s) h t +
      (s * t - c * h) * (--(&13 / &50) * c - (u + a)) +
      (c * (s * t - c * h) / s) * (s - (v + a))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[c1092mpbes_bottomGap; c1092mpbes_bottomValue; c1092mpbes_bottomPlusA;
        c1092mpbes_bottomPlusB; c1092scs_b] THEN
      UNDISCH_TAC `~(s = &0)` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
      CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN
     `c1092mpbes_leftGap a c s (u + a) (v + a) h t =
      c1092mpbes_leftValue a (c1092mpbc_leftPlusA a c s) (c1092mpbc_leftPlusB a c s) h t +
      (s * t - c * h) * ((u + a) - (a - c - s)) +
      (s * (s * t - c * h) / c) * (s - (v + a))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[c1092mpbes_leftGap; c1092mpbes_leftValue; c1092mpbc_leftPlusA;
        c1092mpbc_leftPlusB; c1092scs_ell] THEN
      UNDISCH_TAC `~(c = &0)` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
      CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= c * (s * t - c * h) / s /\ &0 <= s * (s * t - c * h) / c`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_DIV) THEN CONJ_TAC) THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    C1092MPBES_PROD1 `&0 <= (s * t - c * h) * (--(&13 / &50) * c - (u + a))` THEN
    C1092MPBES_PROD1 `&0 <= (c * (s * t - c * h) / s) * (s - (v + a))` THEN
    C1092MPBES_PROD1 `&0 <= (s * t - c * h) * ((u + a) - (a - c - s))` THEN
    C1092MPBES_PROD1 `&0 <= (s * (s * t - c * h) / c) * (s - (v + a))` THEN
    CONJ_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s * t - c * h <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`; `t:real`]
    C1092MPBES_BOTTOM_MINUS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`; `t:real`]
    C1092MPBES_LEFT_MINUS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `max (s * t - c * h) (&0) = &0 /\ max (c * h - s * t) (&0) = c * h - s * t`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_max] THEN CONJ_TAC THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `c1092mpbes_bottomGap a c s (u + a) (v + a) h t =
    c1092mpbes_bottomValue a (c1092mpbc_bottomA a c s) (c1092mpbc_bottomB a c s) h t +
    (--(s * t - c * h)) * ((u + a) - (a - c - s)) +
    (--c * (s * t - c * h) / s) * ((v + a) - (a + (&14 / &25) * s - c))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[c1092mpbes_bottomGap; c1092mpbes_bottomValue; c1092mpbc_bottomA;
      c1092mpbc_bottomB; c1092scs_b] THEN
    UNDISCH_TAC `~(s = &0)` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `c1092mpbes_leftGap a c s (u + a) (v + a) h t =
    c1092mpbes_leftValue a (c1092mpbc_leftMinusA a c s) (c1092mpbc_leftMinusB a c s) h t +
    (--(s * t - c * h)) * (--(&13 / &50) * c - (u + a)) +
    (--s * (s * t - c * h) / c) * ((v + a) - (a + (&14 / &25) * s - c))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[c1092mpbes_leftGap; c1092mpbes_leftValue; c1092mpbc_leftMinusA;
      c1092mpbc_leftMinusB; c1092scs_ell] THEN
    UNDISCH_TAC `~(c = &0)` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= --c * (s * t - c * h) / s /\ &0 <= --s * (s * t - c * h) / c`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `--x * y / z = x * --y / z`] THEN CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_DIV) THEN CONJ_TAC) THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MPBES_PROD1 `&0 <= (--(s * t - c * h)) * ((u + a) - (a - c - s))` THEN
  C1092MPBES_PROD1 `&0 <= (--c * (s * t - c * h) / s) * ((v + a) - (a + (&14 / &25) * s - c))` THEN
  C1092MPBES_PROD1 `&0 <= (--(s * t - c * h)) * (--(&13 / &50) * c - (u + a))` THEN
  C1092MPBES_PROD1 `&0 <= (--s * (s * t - c * h) / c) * ((v + a) - (a + (&14 / &25) * s - c))` THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;
