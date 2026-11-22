(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointQuadraticArc.lean          *)
(* (namespace N12Compact.C1092MPPMCrosspointSupport.QuadraticArc).  Exact    *)
(* sine interpolation of a quadratic plus a linear functional on the unit   *)
(* arc.  cosH / sinH: c1092sps_cosH / c1092sps_sinH.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundArc.ml";;

(* Lean: sum3 / pair3 / triple3 (definitions) *)
let c1092mpqa_sum3 = new_definition
 `c1092mpqa_sum3 (q:real) (z:real) (r:real) = q + z + r`;;
let c1092mpqa_pair3 = new_definition
 `c1092mpqa_pair3 (q:real) (z:real) (r:real) = q * z + q * r + z * r`;;
let c1092mpqa_triple3 = new_definition
 `c1092mpqa_triple3 (q:real) (z:real) (r:real) = q * z * r`;;

(* Lean: X / Y / Z (definitions) *)
let c1092mpqa_X = new_definition
 `c1092mpqa_X (q:real) (z:real) (r:real) =
    &1 - (c1092mpqa_sum3 q z r) pow 2 - (c1092mpqa_pair3 q z r) pow 2 +
    (c1092mpqa_triple3 q z r) pow 2`;;
let c1092mpqa_Y = new_definition
 `c1092mpqa_Y (q:real) (z:real) (r:real) =
    c1092mpqa_sum3 q z r - c1092mpqa_triple3 q z r * c1092mpqa_pair3 q z r`;;
let c1092mpqa_Z = new_definition
 `c1092mpqa_Z (q:real) (z:real) (r:real) =
    (&1 + q pow 2) * (&1 + z pow 2) * (&1 + r pow 2)`;;

(* Lean: remainder (definition) *)
let c1092mpqa_remainder = new_definition
 `c1092mpqa_remainder (a:real) (b:real) (C:real) (q:real) (z:real) (r:real) =
    a * c1092mpqa_X q z r + &2 * b * c1092mpqa_Y q z r - C * c1092mpqa_Z q z r`;;

(* Lean: value (definition) *)
let c1092mpqa_value = new_definition
 `c1092mpqa_value (a:real) (b:real) (C:real) (A:real) (B:real) (z:real) =
    a * (c1092sps_cosH z) pow 2 + b * c1092sps_cosH z * c1092sps_sinH z + C +
    A * c1092sps_cosH z + B * c1092sps_sinH z`;;

(* numerator of value: value z * (1 + z^2)^2 *)
let c1092mpqa_num = new_definition
 `c1092mpqa_num (a:real) (b:real) (C:real) (A:real) (B:real) (z:real) =
    a * (&1 - z pow 2) pow 2 + &2 * b * z * (&1 - z pow 2) + C * (&1 + z pow 2) pow 2 +
    (A * (&1 - z pow 2) + &2 * B * z) * (&1 + z pow 2)`;;

let C1092MPQA_VALUE_NUM = prove
 (`forall a b C A B z. c1092mpqa_value a b C A B z * (&1 + z pow 2) pow 2 =
                 c1092mpqa_num a b C A B z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1092mpqa_value; c1092mpqa_num; c1092sps_cosH; c1092sps_sinH] THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_NZ) THEN CONV_TAC REAL_FIELD);;

(* the exact interpolation identity of nonnegative, cleared of denominators *)
let C1092MPQA_IDENTITY = prove
 (`forall a b C A B q z r.
     (r - q) * (&1 + q * r) * (&1 + q pow 2) * (&1 + r pow 2) * c1092mpqa_num a b C A B z =
     (&1 + z pow 2) * (&1 + r pow 2) * (r - z) * (&1 + r * z) * c1092mpqa_num a b C A B q +
     (&1 + z pow 2) * (&1 + q pow 2) * (z - q) * (&1 + z * q) * c1092mpqa_num a b C A B r +
     (r - q) * &2 * (z - q) * (r - z) * c1092mpqa_remainder a b C q z r`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1092mpqa_num; c1092mpqa_remainder; c1092mpqa_X; c1092mpqa_Y;
              c1092mpqa_Z; c1092mpqa_sum3; c1092mpqa_pair3; c1092mpqa_triple3] THEN
  CONV_TAC REAL_RING);;

let C1092MPQA_LIN_TAC =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092MPQA_POS_TAC =
  REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE (MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC) ORELSE
   C1092MPQA_LIN_TAC);;

let C1092MPQA_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC);;

(* Lean: nonnegative *)
let C1092MPQA_NONNEGATIVE = prove
 (`forall a b C A B q z r.
     &0 <= q /\ q <= z /\ z <= r /\
     &0 <= c1092mpqa_remainder a b C q z r /\
     &0 <= c1092mpqa_value a b C A B q /\ &0 <= c1092mpqa_value a b C A B r
     ==> &0 <= c1092mpqa_value a b C A B z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `q:real = r` THENL
   [SUBGOAL_THEN `z:real = q` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r - q /\ &0 <= r - z /\ &0 <= z - q` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun v -> MP_TAC(SPEC v C1092SPS_HALF_DEN_POS) THEN DISCH_TAC)
    [`q:real`; `z:real`; `r:real`] THEN
  MP_TAC(SPECL [`q:real`; `r:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`r:real`; `z:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`z:real`; `q:real`] REAL_LE_MUL) THEN
  REPEAT(ANTS_TAC THENL [C1092MPQA_LIN_TAC; DISCH_TAC]) THEN
  SUBGOAL_THEN `&0 < &1 + q * r /\ &0 <= &1 + r * z /\ &0 <= &1 + z * q`
    STRIP_ASSUME_TAC THENL [C1092MPQA_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092mpqa_num a b C A B q /\ &0 <= c1092mpqa_num a b C A B r`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM C1092MPQA_VALUE_NUM] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092mpqa_num a b C A B z` MP_TAC THENL
   [MATCH_MP_TAC C1092MPQA_CANCEL THEN
    EXISTS_TAC `(r - q) * (&1 + q * r) * (&1 + q pow 2) * (&1 + r pow 2)` THEN
    CONJ_TAC THENL [C1092MPQA_POS_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; C1092MPQA_IDENTITY] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN C1092MPQA_POS_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM C1092MPQA_VALUE_NUM] THEN DISCH_TAC THEN
  MATCH_MP_TAC C1092MPQA_CANCEL THEN EXISTS_TAC `(&1 + z pow 2) pow 2` THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]);;
