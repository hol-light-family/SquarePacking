(* ========================================================================= *)
(* Port of Compact/Geometry/CornerOuterOrderMonotone.lean (Jatloe).           *)
(* Two continuous order comparisons for the bottom-to-wall coupling, via a  *)
(* half-angle change of variables.                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* Lean: denominator, cross, F, G (definitions) *)
let coom_denominator = new_definition
 `coom_denominator (q:real) t = (&1 + q) * (&1 + t)`;;
let coom_cross = new_definition
 `coom_cross (p:real) q d t = d * q - p * t`;;
let coom_f = new_definition
 `coom_f (p:real) q d t = coom_denominator q t * (d - p) + p * d * (q - t)`;;
let coom_g = new_definition
 `coom_g (p:real) q d t =
    coom_denominator q t * (&2 * coom_cross p q d t - (q - t)) -
    q * t * ((d - p) + coom_cross p q d t)`;;

(* Lean: half_angle (private), with x = q / (1 + p) *)
let COOM_HALF_ANGLE = prove
 (`forall p q. c977cc_normal p q
     ==> &0 <= q / (&1 + p) /\ q / (&1 + p) <= &1 / &2 /\
         p * (&1 + (q / (&1 + p)) pow 2) = &1 - (q / (&1 + p)) pow 2 /\
         q * (&1 + (q / (&1 + p)) pow 2) = &2 * (q / (&1 + p))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < &1 + p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
   UNDISCH_TAC `&0 < &1 + p` THEN UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN
   CONV_TAC REAL_FIELD;
   UNDISCH_TAC `&0 < &1 + p` THEN UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN
   CONV_TAC REAL_FIELD]);;

(* Lean: P, Q (private definitions) *)
let coom_p = new_definition
 `coom_p (x:real) y = (x + y) * (&1 - x) * (&1 - y) + &4 * x pow 2 * y pow 2`;;
let coom_q = new_definition
 `coom_q (x:real) y =
    (x - y) + x pow 2 * (&1 - x - x pow 2) + x pow 3 * y * (&2 - &3 * x + &3 * y) +
    y pow 2 * (&3 * x pow 2 + x + &1) + &2 * x * y`;;

(* Lean: polynomial_nonnegative (private) *)
let COOM_POLYNOMIAL_NONNEGATIVE = prove
 (`forall x y. &0 <= y /\ y <= x /\ x <= &1 / &2 ==> &0 <= coom_p x y /\ &0 <= coom_q x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &1 - x - x pow 2` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= x * (&1 / &2 - x)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &3 * x pow 2 + x + &1` ASSUME_TAC THENL
  [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[coom_p; coom_q] THEN CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC);;

(* Lean: differences *)
let COOM_DIFFERENCES = prove
 (`forall p q d t. c977cc_normal p q /\ c977cc_normal d t /\ t <= q
     ==> &0 <= coom_g p q d t - coom_f p q d t /\
         &0 <= p * coom_f p q d t + q * coom_g p q d t -
               coom_denominator q t * coom_cross p q d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`; `d:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`] COOM_HALF_ANGLE) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] COOM_HALF_ANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `t / (&1 + d) <= q / (&1 + p)` MP_TAC THENL
  [SUBGOAL_THEN `&0 < &1 + d /\ &0 < &1 + p` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
     REAL_ARITH `&0 < a ==> (x / b) * a = (x * a) / b`] THEN
   SUBGOAL_THEN `&0 <= (q - t) * (&1 + p) /\ &0 <= q * (d - p)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`t / (&1 + d)`,`y:real`) THEN SPEC_TAC(`q / (&1 + p)`,`x:real`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2 /\ &0 < &1 + y pow 2` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 < &1 + a`) THEN
   REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `p = (&1 - x pow 2) / (&1 + x pow 2) /\ q = (&2 * x) / (&1 + x pow 2) /\
                d = (&1 - y pow 2) / (&1 + y pow 2) /\ t = (&2 * y) / (&1 + y pow 2)`
  STRIP_ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `y:real`] COOM_POLYNOMIAL_NONNEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * (&1 + x) * (x - y) * (&1 + y)` ASSUME_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[coom_f; coom_g; coom_denominator; coom_cross] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && mem (lhs(concl th)) [`p:real`;`q:real`;`d:real`;`t:real`]
    then SUBST1_TAC th else NO_TAC)) THEN
  CONJ_TAC THEN MATCH_MP_TAC C977CSB_LE_BY_POS THENL
  [EXISTS_TAC `(&1 + x pow 2) pow 2 * (&1 + y pow 2) pow 2`;
   EXISTS_TAC `(&1 + x pow 2) pow 3 * (&1 + y pow 2) pow 2`] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  (CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REWRITE_TAC[]; ALL_TAC]) THENL
  [SUBGOAL_THEN `forall e. e = &2 * (&1 + x) * (x - y) * (&1 + y) * coom_p x y ==> &0 <= e`
   MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]; ALL_TAC];
   SUBGOAL_THEN `forall e. e = &2 * (&1 + x) * (x - y) * (&1 + y) * coom_q x y ==> &0 <= e`
   MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]; ALL_TAC]] THEN
  REWRITE_TAC[coom_p; coom_q] THEN
  UNDISCH_TAC `&0 < &1 + x pow 2` THEN UNDISCH_TAC `&0 < &1 + y pow 2` THEN
  CONV_TAC REAL_FIELD);;
