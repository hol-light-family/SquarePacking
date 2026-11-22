(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974LowerFaceScalars.lean      *)
(* (namespace N12Compact.Completion.OtherCases.C983.C974LowerFace).          *)
(* Scalar identities in section 2 of C974-THREE-SQUARE-ENDING.  Lean's       *)
(* `let x := s/(1+c)` is written out; the private P, Q, R become             *)
(* definitions c983lfs_p, c983lfs_q, c983lfs_r.                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;

let C983LFS_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let C983LFS_POS_CANCEL = prove
 (`forall k x. &0 < k /\ &0 < x * k ==> &0 < x`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let C983LFS_NONNEG_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= x * k ==> &0 <= x`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let C983LFS_DEN_TAC =
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC(REAL_ARITH `forall z. &0 <= z ==> &0 < &1 + z`) THEN REWRITE_TAC[REAL_LE_POW_2]);;

(* Lean: half_data *)
let C983LFS_HALF_DATA = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ &4 * s < &3 * c
         ==> &0 < s / (&1 + c) /\ s / (&1 + c) < &1 / &3 /\
             s * (s / (&1 + c)) = &1 - c /\
             c = (&1 - (s / (&1 + c)) pow 2) / (&1 + (s / (&1 + c)) pow 2) /\
             s = &2 * (s / (&1 + c)) / (&1 + (s / (&1 + c)) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 * s < &1 + c` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    NLIN_FACTS_TAC [] [`&4 / &5 < c`; `&0 <= (&3 * s - (&1 + c)) * (&3 * s + (&1 + c))`] THEN
    NLIN_TAC []; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `&0 < &1 + c` THEN
    CONV_TAC REAL_FIELD;
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `&0 < &1 + c` THEN
    CONV_TAC REAL_FIELD;
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `&0 < &1 + c` THEN
    CONV_TAC REAL_FIELD]);;

(* Lean: cosine_lower *)
let C983LFS_COSINE_LOWER = prove
 (`forall d t. &0 < d /\ &0 < t /\ d pow 2 + t pow 2 = &1 /\ &3 * t < &2 * d ==> &83 / &100 < d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < (&2 * d - &3 * t) * (&2 * d + &3 * t)`] THEN
  NLIN_TAC []);;

(* Lean: denominator_pos (private) *)
let C983LFS_DENOMINATOR_POS = prove
 (`forall x z. &0 < (&1 + x pow 2) * (&1 + z pow 2)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN C983LFS_DEN_TAC);;

(* Lean: sigma_identity *)
let C983LFS_SIGMA_IDENTITY = prove
 (`forall l h d t x z. l = (&1 - x pow 2) / (&1 + x pow 2) /\ h = &2 * x / (&1 + x pow 2) /\
                 d = (&1 - z pow 2) / (&1 + z pow 2) /\ t = &2 * z / (&1 + z pow 2)
     ==> (h * d - l * t) * ((&1 + x pow 2) * (&1 + z pow 2)) = &2 * (x - z) * (&1 + x * z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST1_TAC) THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2 /\ &0 < &1 + z pow 2` MP_TAC THENL
   [C983LFS_DEN_TAC; CONV_TAC REAL_FIELD]);;

(* Lean: sine_identity *)
let C983LFS_SINE_IDENTITY = prove
 (`forall (l:real) h (d:real) t x z. h = &2 * x / (&1 + x pow 2) /\ t = &2 * z / (&1 + z pow 2)
     ==> (h - t) * ((&1 + x pow 2) * (&1 + z pow 2)) = &2 * (x - z) * (&1 - x * z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST1_TAC) THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2 /\ &0 < &1 + z pow 2` MP_TAC THENL
   [C983LFS_DEN_TAC; CONV_TAC REAL_FIELD]);;

(* Lean: forward_w_large *)
let C983LFS_FORWARD_W_LARGE = prove
 (`forall l h d t x z. &0 < d /\ &0 < h /\ &0 < t /\ h < &1 /\ t < &1 /\
     &0 < x /\ &0 < z /\ x < &1 / &3 /\ z < &1 / &3 /\ z <= x /\
     h * x = &1 - l /\ t * z = &1 - d /\ x * (&1 + l) = h /\ z * (&1 + d) = t /\
     h = &2 * x / (&1 + x pow 2) /\ t = &2 * z / (&1 + z pow 2)
     ==> --z * (&1 - t) <= (l * d + h * t) * (&1 - x) + (h * d - l * t) - d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `h:real`; `d:real`; `t:real`; `x:real`; `z:real`]
    C983LFS_SINE_IDENTITY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C983LFS_DENOMINATOR_POS) THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < x * (&1 / &3 - z)`; `x * z < &1`] THEN
  SUBGOAL_THEN `t <= h` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= h - t ==> t <= h`) THEN
    MATCH_MP_TAC C983LFS_NONNEG_CANCEL THEN
    EXISTS_TAC `(&1 + x pow 2) * (&1 + z pow 2)` THEN ASM_REWRITE_TAC[] THEN
    NLIN_FACTS_TAC [] [`&0 <= (x - z) * (&1 - x * z)`] THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l * d + h * t) * (&1 - x) + (h * d - l * t) - d = (&1 - h) * (d * x - t)`
    SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`h * x = &1 - l`; `x * (&1 + l) = h`] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `d * z - t = --z` ASSUME_TAC THENL
   [UNDISCH_TAC `z * (&1 + d) = t` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= d * x - t` THENL
   [NLIN_FACTS_TAC [] [`&0 <= (&1 - h) * (d * x - t)`; `&0 < z * (&1 - t)`] THEN
    NLIN_TAC ~deg2:false [];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    NLIN_FACTS_TAC []
     [`&0 <= (h - t) * --(d * x - t)`; `&0 <= d * (x - z)`;
      `&0 <= (&1 - t) * (d * (x - z))`] THEN
    NLIN_TAC ~deg2:false [C983LFS_EQ_HINT `&1 - t` (ASSUME `d * z - t = --z`)]]);;

(* Lean: P (private def) *)
let C983LFS_P_DEF = new_definition
 `c983lfs_p (x:real) (z:real) = x pow 2 * (&1 + z pow 2) pow 2 +
    x * (--(z pow 3) - &6 * z pow 2 + z - &2) - z pow 4 + &2 * z pow 3 - &3 * z pow 2 - &2 * z`;;

(* Lean: p_negative (private) *)
let C983LFS_P_NEGATIVE = prove
 (`forall x z. &0 < x /\ &0 < z /\ x < &1 / &3 /\ z < &1 / &3 ==> c983lfs_p x z < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C983LFS_P_DEF] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `x:real`; SQ_NONNEG `z:real`; SQ_NONNEG `z - &1`]
   [`z pow 2 <= &1 / &9`; `&0 <= (&1 / &9 - z pow 2) * (&10 / &9 + (&1 + z pow 2))`;
    `(&1 + z pow 2) pow 2 <= &4 / &3`; `x pow 2 <= x / &3`;
    `&0 <= x pow 2 * (&4 / &3 - (&1 + z pow 2) pow 2)`;
    `x pow 2 * (&1 + z pow 2) pow 2 <= &4 * x / &9`;
    `&0 <= z pow 3`; `--(z pow 3) - &6 * z pow 2 + z - &2 <= --(&5 / &3)`;
    `&0 <= x * (--(&5 / &3) - (--(z pow 3) - &6 * z pow 2 + z - &2))`;
    `&0 <= z pow 2 * ((z - &1) pow 2 + &2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: forward_k_large *)
let C983LFS_FORWARD_K_LARGE = prove
 (`forall l h d t x z. &0 < x /\ &0 < z /\ x < &1 / &3 /\ z < &1 / &3 /\ z <= x /\
     l = (&1 - x pow 2) / (&1 + x pow 2) /\ h = &2 * x / (&1 + x pow 2) /\
     d = (&1 - z pow 2) / (&1 + z pow 2) /\ t = &2 * z / (&1 + z pow 2)
     ==> &0 <= (l * d + h * t) * z * (&1 - t) + (h * d - l * t) * (&1 - d / &2) -
              x * (&1 - h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C983LFS_P_NEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC C983LFS_NONNEG_CANCEL THEN
  EXISTS_TAC `(&1 + x pow 2) * (&1 + z pow 2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [C983LFS_DEN_TAC; MATCH_MP_TAC REAL_POW_LT THEN C983LFS_DEN_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `((l * d + h * t) * z * (&1 - t) + (h * d - l * t) * (&1 - d / &2) -
                 x * (&1 - h)) * ((&1 + x pow 2) * (&1 + z pow 2) pow 2) =
                --(x - z) * c983lfs_p x z` SUBST1_TAC THENL
   [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_var(lhs(concl th))) o
      check (fun th -> is_eq(concl th)))) THEN
    REWRITE_TAC[C983LFS_P_DEF] THEN
    SUBGOAL_THEN `&0 < &1 + x pow 2 /\ &0 < &1 + z pow 2` MP_TAC THENL
     [C983LFS_DEN_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= (x - z) * --(c983lfs_p x z)`] THEN NLIN_TAC ~deg2:false []);;

(* Lean: Q (private def) *)
let C983LFS_Q_DEF = new_definition
 `c983lfs_q (x:real) (z:real) = x pow 2 * (z pow 2 - &1) + &2 * x * (z + &1) + (&1 - z) pow 2`;;

(* Lean: forward_w_small *)
let C983LFS_FORWARD_W_SMALL = prove
 (`forall l h d t x z. &0 < x /\ &0 < z /\ x < &1 / &3 /\ x < z /\
     l = (&1 - x pow 2) / (&1 + x pow 2) /\ h = &2 * x / (&1 + x pow 2) /\
     d = (&1 - z pow 2) / (&1 + z pow 2) /\ t = &2 * z / (&1 + z pow 2)
     ==> &0 < (l * d + h * t) * (&1 - x) - d + z * (&1 - t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c983lfs_q x z` ASSUME_TAC THENL
   [REWRITE_TAC[C983LFS_Q_DEF] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `&1 - z`; SQ_NONNEG `x:real`; SQ_NONNEG `z:real`]
     [`&0 < x * (&2 - x)`; `&0 <= x pow 2`; `&0 <= z pow 2`; `&0 <= x pow 2 * z pow 2`;
      `&0 < x * z`] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - z`]; ALL_TAC] THEN
  MATCH_MP_TAC C983LFS_POS_CANCEL THEN
  EXISTS_TAC `(&1 + x pow 2) * (&1 + z pow 2)` THEN
  REWRITE_TAC[C983LFS_DENOMINATOR_POS] THEN
  SUBGOAL_THEN `((l * d + h * t) * (&1 - x) - d + z * (&1 - t)) *
                ((&1 + x pow 2) * (&1 + z pow 2)) = --(x - z) * c983lfs_q x z` SUBST1_TAC THENL
   [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_var(lhs(concl th))) o
      check (fun th -> is_eq(concl th)))) THEN
    REWRITE_TAC[C983LFS_Q_DEF] THEN
    SUBGOAL_THEN `&0 < &1 + x pow 2 /\ &0 < &1 + z pow 2` MP_TAC THENL
     [C983LFS_DEN_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 < (z - x) * c983lfs_q x z`] THEN NLIN_TAC ~deg2:false []);;

(* Lean: R (private def) *)
let C983LFS_R_DEF = new_definition
 `c983lfs_r (x:real) (z:real) = x pow 2 * (&1 + z pow 2) pow 2 +
    &2 * x * (z pow 3 - &3 * z pow 2 + z - &1) - z pow 4 + &2 * z pow 3 - &2 * z + &1`;;

(* Lean: r_positive (private) *)
let C983LFS_R_POSITIVE = prove
 (`forall x z. &0 < x /\ &0 < z /\ x < z /\ z <= &2 / &7 ==> &0 < c983lfs_r x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C983LFS_R_DEF] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `z:real`]
   [`z pow 2 <= &4 / &49`; `z pow 3 <= &8 / &343`; `&0 <= z pow 3`;
    `(&1 + z pow 2) pow 2 <= &100 / &81`;
    `&0 <= (x + z) * (&100 / &81 - (&1 + z pow 2) pow 2)`;
    `(x + z) * (&1 + z pow 2) pow 2 <= &200 / &243`;
    `(x + z) * (&1 + z pow 2) pow 2 + &2 * (z pow 3 - &3 * z pow 2 + z - &1) < &0`;
    `&0 < (z - x) * --((x + z) * (&1 + z pow 2) pow 2 + &2 * (z pow 3 - &3 * z pow 2 + z - &1))`;
    `&0 < &1 - &3 * z - z pow 2 - z pow 3`;
    `&0 < (&1 - z) * (&1 + z pow 2)`;
    `&0 < ((&1 - z) * (&1 + z pow 2)) * (&1 - &3 * z - z pow 2 - z pow 3)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: forward_k_small *)
let C983LFS_FORWARD_K_SMALL = prove
 (`forall l h d t x z. &0 < x /\ &0 < z /\ x < z /\ z <= &2 / &7 /\
     l = (&1 - x pow 2) / (&1 + x pow 2) /\ h = &2 * x / (&1 + x pow 2) /\
     d = (&1 - z pow 2) / (&1 + z pow 2) /\ t = &2 * z / (&1 + z pow 2)
     ==> &0 < (l * d + h * t) * z * (&1 - t) - x * (&1 - h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C983LFS_R_POSITIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC C983LFS_POS_CANCEL THEN
  EXISTS_TAC `(&1 + x pow 2) * (&1 + z pow 2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [C983LFS_DEN_TAC; MATCH_MP_TAC REAL_POW_LT THEN C983LFS_DEN_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `((l * d + h * t) * z * (&1 - t) - x * (&1 - h)) *
                ((&1 + x pow 2) * (&1 + z pow 2) pow 2) = --(x - z) * c983lfs_r x z`
    SUBST1_TAC THENL
   [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_var(lhs(concl th))) o
      check (fun th -> is_eq(concl th)))) THEN
    REWRITE_TAC[C983LFS_R_DEF] THEN
    SUBGOAL_THEN `&0 < &1 + x pow 2 /\ &0 < &1 + z pow 2` MP_TAC THENL
     [C983LFS_DEN_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 < (z - x) * c983lfs_r x z`] THEN NLIN_TAC ~deg2:false []);;
