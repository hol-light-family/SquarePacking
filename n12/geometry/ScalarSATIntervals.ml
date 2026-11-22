(* ========================================================================= *)
(* Port of Compact/Geometry/ScalarSATIntervals.lean (N12Compact.SATIntervals)*)
(* Small interval-intersection lemmas for the necessity direction of SAT.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: between_four *)
let SSI_BETWEEN_FOUR = prove
 (`forall l0 l1 l2 l3 u0 u1 u2 u3:real.
     (l0 < u0 /\ l0 < u1 /\ l0 < u2 /\ l0 < u3) /\
     (l1 < u0 /\ l1 < u1 /\ l1 < u2 /\ l1 < u3) /\
     (l2 < u0 /\ l2 < u1 /\ l2 < u2 /\ l2 < u3) /\
     (l3 < u0 /\ l3 < u1 /\ l3 < u2 /\ l3 < u3)
     ==> exists y. (l0 < y /\ l1 < y /\ l2 < y /\ l3 < y) /\
             (y < u0 /\ y < u1 /\ y < u2 /\ y < u3)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(max l0 (max l1 (max l2 l3)) + min u0 (min u1 (min u2 u3))) / &2` THEN
  REWRITE_TAC[real_max; real_min] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN RASM_ARITH_TAC);;

(* Lean: between_three *)
let SSI_BETWEEN_THREE = prove
 (`forall l0 l1 l2 u0 u1 u2:real.
     (l0 < u0 /\ l0 < u1 /\ l0 < u2) /\
     (l1 < u0 /\ l1 < u1 /\ l1 < u2) /\
     (l2 < u0 /\ l2 < u1 /\ l2 < u2)
     ==> exists x. (l0 < x /\ l1 < x /\ l2 < x) /\ (x < u0 /\ x < u1 /\ x < u2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l0:real`; `l1:real`; `l2:real`; `l2:real`;
                `u0:real`; `u1:real`; `u2:real`; `u2:real`] SSI_BETWEEN_FOUR) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* helper: comparison of two quotients by positive denominators *)
let SSI_DIV_LT_DIV = prove
 (`forall p q d e. &0 < d /\ &0 < e ==> (p / d < q / e <=> p * e < q * d)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  REWRITE_TAC[real_div; REAL_ARITH `(q * i) * d = (q * d) * i:real`] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ]);;

let SSI_ABS_LT = REAL_ARITH `forall x h. abs x < h <=> --h < x /\ x < h`;;

(* Lean: positive_y_intervals *)
let SSI_POSITIVE_Y_INTERVALS = prove
 (`forall c s X Y U V.
     &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < &1 + c + s /\ abs Y < &1 + c + s /\
     abs U < &1 + c + s /\ abs V < &1 + c + s
     ==> exists y. (--(&1) < y /\ (U - &1 - c) / s < y /\ (V - &1 - s) / c < y /\
              Y - c - s < y) /\
             (y < &1 /\ y < (U + &1 + c) / s /\ y < (V + &1 + s) / c /\
              y < Y + c + s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SSI_ABS_LT; REAL_POW_2] THEN STRIP_TAC THEN
  MATCH_MP_TAC SSI_BETWEEN_FOUR THEN
  SIMP_TAC[SSI_DIV_LT_DIV; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s:real`]);;
