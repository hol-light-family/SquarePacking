(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointQuadraticRemainders.lean   *)
(* (namespace N12Compact.C1092MPPMCrosspointSupport.QuadraticArc).  Three    *)
(* full-interval quadratic interpolation margins needed by G01/G11.          *)
(* Private Box structure: a conjunction (C1092MPQR_BOX).                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointQuadraticArc.ml";;

(* Lean: one / mixed (private definitions) *)
let c1092mpqr_one = new_definition
 `c1092mpqr_one (a:real) (b:real) (c:real) (A:real) (B:real) (C:real) =
    A * b * c + a * B * c + a * b * C`;;
let c1092mpqr_mixed = new_definition
 `c1092mpqr_mixed (a:real) (b:real) (c:real) (A:real) (B:real) (C:real)
                  (x:real) (y:real) (z:real) =
    a * B * z + a * y * C + A * b * z + A * y * c + x * b * C + x * B * c`;;

(* nonnegativity of products / sums / powers / quotients of nonnegatives *)
let rec C1092MPQR_POS_TAC g =
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   MATCH_ACCEPT_TAC REAL_LE_POW_2 ORELSE
   (CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) ORELSE
   (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C1092MPQR_POS_TAC) ORELSE
   (MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN C1092MPQR_POS_TAC) ORELSE
   (MATCH_MP_TAC REAL_POW_LE THEN C1092MPQR_POS_TAC) ORELSE
   (MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN C1092MPQR_POS_TAC) ORELSE
   RASM_ARITH_TAC) g;;

let C1092MPQR_REMAINDER_SCALE = prove
 (`forall k a b C q z r. k * c1092mpqa_remainder a b C q z r =
                   c1092mpqa_remainder (k * a) (k * b) (k * C) q z r`,
  REWRITE_TAC[c1092mpqa_remainder] THEN REAL_ARITH_TAC);;

let C1092MPQR_COSH_SCALE = prove
 (`forall p. (&1 + p pow 2) * c1092sps_cosH p = &1 - p pow 2 /\
       (&1 + p pow 2) * c1092sps_sinH p = &2 * p`,
  GEN_TAC THEN REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
  MP_TAC(SPEC `p:real` C1092SPS_HALF_DEN_NZ) THEN CONV_TAC REAL_FIELD);;

let C1092MPQR_CENTRAL_IDENTITY = prove
 (`forall p q z r.
     p pow 6 * c1092mpqa_remainder (&1 - p pow 2) (&2 * p) (&2 * p) q z r =
     (&1 - &2 * p - p pow 2) * (p - q) pow 2 * (p - z) pow 2 * (p - r) pow 2 +
     (&1 - p) pow 2 * c1092mpqr_one ((p - q) pow 2) ((p - z) pow 2) ((p - r) pow 2)
        (&2 * q * (p - q)) (&2 * z * (p - z)) (&2 * r * (p - r)) +
     ((&1 - p) pow 2 * (&1 + p pow 2)) *
        c1092mpqr_one ((p - q) pow 2) ((p - z) pow 2) ((p - r) pow 2)
        (q pow 2) (z pow 2) (r pow 2) +
     ((&1 - p) pow 2 + (&3 / &2) * p pow 2 + p pow 4 / &2) *
        c1092mpqr_one (&2 * q * (p - q)) (&2 * z * (p - z)) (&2 * r * (p - r))
        ((p - q) pow 2) ((p - z) pow 2) ((p - r) pow 2) +
     ((&1 - p) pow 2 + &2 * p pow 2 * (&1 - p + p pow 2)) *
        c1092mpqr_mixed ((p - q) pow 2) ((p - z) pow 2) ((p - r) pow 2)
        (&2 * q * (p - q)) (&2 * z * (p - z)) (&2 * r * (p - r))
        (q pow 2) (z pow 2) (r pow 2) +
     ((&1 - p) pow 2 * (&1 + p pow 2) pow 2) *
        (c1092mpqr_one (q pow 2) (z pow 2) (r pow 2)
           ((p - q) pow 2) ((p - z) pow 2) ((p - r) pow 2) +
         c1092mpqr_one (q pow 2) (z pow 2) (r pow 2)
           (&2 * q * (p - q)) (&2 * z * (p - z)) (&2 * r * (p - r))) +
     ((&1 - p) pow 2 + (&5 / &2) * p pow 2 + (&3 / &2) * p pow 4) *
        (&2 * q * (p - q)) * (&2 * z * (p - z)) * (&2 * r * (p - r)) +
     ((&1 - p) pow 2 + p pow 2 / &2 + &2 * p pow 2 * (&1 - p) + &3 * p pow 4 +
      p pow 6 / &2) *
        c1092mpqr_one (&2 * q * (p - q)) (&2 * z * (p - z)) (&2 * r * (p - r))
        (q pow 2) (z pow 2) (r pow 2) +
     ((&1 - &2 * p - p pow 2) * (&1 + p pow 2) pow 3) *
        q pow 2 * z pow 2 * r pow 2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1092mpqa_remainder; c1092mpqa_X; c1092mpqa_Y; c1092mpqa_Z;
    c1092mpqa_sum3; c1092mpqa_pair3; c1092mpqa_triple3;
    c1092mpqr_one; c1092mpqr_mixed] THEN
  CONV_TAC REAL_RING);;

(* Lean: central_remainder *)
let C1092MPQR_CENTRAL_REMAINDER = prove
 (`forall p q z r. &0 <= p /\ p <= &1 /\ &0 <= &1 - &2 * p - p pow 2 /\
     &0 <= q /\ q <= p /\ &0 <= z /\ z <= p /\ &0 <= r /\ r <= p
     ==> &0 <= c1092mpqa_remainder (c1092sps_cosH p) (c1092sps_sinH p)
                                   (c1092sps_sinH p) q z r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `p = &0` THENL
   [SUBGOAL_THEN `q = &0 /\ z = &0 /\ r = &0` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[c1092mpqa_remainder; c1092mpqa_X; c1092mpqa_Y; c1092mpqa_Z;
      c1092mpqa_sum3; c1092mpqa_pair3; c1092mpqa_triple3;
      c1092sps_cosH; c1092sps_sinH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC C1092MPQA_CANCEL THEN
  EXISTS_TAC `p pow 6 * (&1 + p pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LT; C1092SPS_HALF_DEN_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p pow 6 * (&1 + p pow 2)) *
                c1092mpqa_remainder (c1092sps_cosH p) (c1092sps_sinH p)
                                    (c1092sps_sinH p) q z r =
                p pow 6 * c1092mpqa_remainder (&1 - p pow 2) (&2 * p) (&2 * p) q z r`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[C1092MPQR_REMAINDER_SCALE; C1092MPQR_COSH_SCALE];
    ALL_TAC] THEN
  REWRITE_TAC[C1092MPQR_CENTRAL_IDENTITY] THEN
  SUBGOAL_THEN `&0 <= &1 - p /\ &0 <= p - q /\ &0 <= p - z /\ &0 <= p - r /\
                &0 <= &1 - p + p pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&1 - p + p pow 2 = (&1 - p) + p pow 2`] THEN
    MP_TAC(SPEC `p:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092mpqr_one; c1092mpqr_mixed] THEN
  C1092MPQR_POS_TAC);;

(* Lean: Box (private structure) and box *)
let C1092MPQR_BOX = prove
 (`forall u q z r. &0 <= u /\ &0 <= q /\ q <= u /\ &0 <= z /\ z <= u /\
     &0 <= r /\ r <= u
     ==> &0 <= c1092mpqa_sum3 q z r /\ c1092mpqa_sum3 q z r <= &3 * u /\
         &0 <= c1092mpqa_pair3 q z r /\ c1092mpqa_pair3 q z r <= &3 * u pow 2 /\
         &0 <= c1092mpqa_triple3 q z r /\ c1092mpqa_triple3 q z r <= u pow 3 /\
         &1 <= c1092mpqa_Z q z r /\ c1092mpqa_Z q z r <= (&1 + u pow 2) pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `q * z <= u * u /\ q * r <= u * u /\ z * r <= u * u /\
                q * q <= u * u /\ z * z <= u * u /\ r * r <= u * u`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q * z) * r <= (u * u) * u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &1 + q pow 2 /\ &1 + q pow 2 <= &1 + u pow 2 /\
                &1 <= &1 + z pow 2 /\ &1 + z pow 2 <= &1 + u pow 2 /\
                &1 <= &1 + r pow 2 /\ &1 + r pow 2 <= &1 + u pow 2`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    MP_TAC(SPEC `q:real` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `r:real` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + q pow 2) * (&1 + z pow 2)) * (&1 + r pow 2) <=
                ((&1 + u pow 2) * (&1 + u pow 2)) * (&1 + u pow 2) /\
                (&1 * &1) * &1 <=
                ((&1 + q pow 2) * (&1 + z pow 2)) * (&1 + r pow 2)`
    MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL2) THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092mpqa_sum3; c1092mpqa_pair3; c1092mpqa_triple3; c1092mpqa_Z] THEN
  SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `x pow 3 = x * x * x`; REAL_POW_2] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_MUL_ASSOC]) THEN ASM_REAL_ARITH_TAC);;

(* Lean: X_lower *)
let C1092MPQR_X_LOWER = prove
 (`forall u q z r. &0 <= u /\ &0 <= q /\ q <= u /\ &0 <= z /\ z <= u /\
     &0 <= r /\ r <= u
     ==> &1 - (&3 * u) pow 2 - (&3 * u pow 2) pow 2 <= c1092mpqa_X q z r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092MPQR_BOX) THEN
  SUBGOAL_THEN `c1092mpqa_sum3 q z r * c1092mpqa_sum3 q z r <= (&3 * u) * (&3 * u) /\
                c1092mpqa_pair3 q z r * c1092mpqa_pair3 q z r <=
                (&3 * u pow 2) * (&3 * u pow 2)`
    MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[c1092mpqa_X; GSYM REAL_POW_2] THEN
  MP_TAC(SPEC `c1092mpqa_triple3 q z r` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

(* Lean: middle_remainder *)
let C1092MPQR_MIDDLE_REMAINDER = prove
 (`forall a b C q z r.
     &0 <= a /\ a <= &1 / &5 /\ &7 / &5 <= b /\ &0 <= C /\ C <= &71 / &100 /\
     &1 / &3 <= q /\ q <= &1 / &2 /\ &1 / &3 <= z /\ z <= &1 / &2 /\
     &1 / &3 <= r /\ r <= &1 / &2
     ==> &0 <= c1092mpqa_remainder a b C q z r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&1 / &2`; `q:real`; `z:real`; `r:real`] C1092MPQR_BOX) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&1 / &2`; `q:real`; `z:real`; `r:real`] C1092MPQR_X_LOWER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1092mpqa_triple3 q z r * c1092mpqa_pair3 q z r <=
                &1 / &8 * &3 / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&29 / &32 <= c1092mpqa_Y q z r` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpqa_Y; c1092mpqa_sum3] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a * (c1092mpqa_X q z r + &29 / &16) /\
                &0 <= (b - &7 / &5) * c1092mpqa_Y q z r /\
                &0 <= C * (&125 / &64 - c1092mpqa_Z q z r)`
    MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092mpqa_remainder] THEN ASM_REAL_ARITH_TAC);;

(* Lean: upper_remainder *)
let C1092MPQR_UPPER_REMAINDER = prove
 (`forall a b q z r.
     &0 <= a /\ a <= &731 / &1000 /\ -- &171 / &500 <= b /\ b <= &0 /\
     &0 <= q /\ q <= &5 / &12 /\ &0 <= z /\ z <= &5 / &12 /\
     &0 <= r /\ r <= &5 / &12
     ==> &0 <= c1092mpqa_remainder a b (-- &1543 / &1000) q z r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&5 / &12`; `q:real`; `z:real`; `r:real`] C1092MPQR_BOX) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&5 / &12`; `q:real`; `z:real`; `r:real`] C1092MPQR_X_LOWER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1092mpqa_Y q z r <= &5 / &4` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mpqa_Y] THEN
    MP_TAC(SPECL [`c1092mpqa_triple3 q z r`; `c1092mpqa_pair3 q z r`]
      REAL_LE_MUL) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a * (c1092mpqa_X q z r + &1921 / &2304) /\
                &0 <= (--b) * (&5 / &4 - c1092mpqa_Y q z r)`
    MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092mpqa_remainder] THEN ASM_REAL_ARITH_TAC);;
