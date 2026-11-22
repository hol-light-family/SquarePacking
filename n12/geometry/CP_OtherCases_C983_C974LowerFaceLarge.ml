(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974LowerFaceLarge.lean        *)
(* (namespace N12Compact.Completion.OtherCases.C983.C974LowerFace).          *)
(* The large-half-angle exclusion, equations (14)--(17).  The private f is   *)
(* c983lfl_fv.  The private derivative lemma f_derivative (used in Lean only  *)
(* to prove f_small by monotonicity) is replaced: f_small is proved          *)
(* directly from the factorisation 8-65x+138x^2-65x^3 = (1-5x)(8-25x+13x^2). *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_HalfAngle.ml";;

let C983LFL_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let C983LFL_DEN = prove
 (`forall x. &0 < &1 + x pow 2`,
  GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `forall z. &0 <= z ==> &0 < &1 + z`) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

(* Lean: f (private def) *)
let C983LFL_F_DEF = new_definition
 `c983lfl_fv (x:real) = (x * (&1 - x) pow 2) / (&1 + x pow 2)`;;

(* Lean: f_small (private; proved without the derivative lemma f_derivative) *)
let C983LFL_F_SMALL = prove
 (`forall x. &0 <= x /\ x <= &1 / &5 ==> c983lfl_fv x <= &8 / &65`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C983LFL_F_DEF] THEN
  MP_TAC(SPEC `x:real` C983LFL_DEN) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  NLIN_FACTS_TAC [] [`&0 <= &1 - &5 * x`; `&0 < &8 - &25 * x + &13 * x pow 2`;
                     `&0 <= (&1 - &5 * x) * (&8 - &25 * x + &13 * x pow 2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: f_uniform (private) *)
let C983LFL_F_UNIFORM = prove
 (`forall x. x <= &1 / &3 ==> c983lfl_fv x < &7 / &50`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C983LFL_F_DEF] THEN
  MP_TAC(SPEC `x:real` C983LFL_DEN) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `x:real`; SQ_NONNEG `x - &75 / &271`]
   [`&0 <= x pow 2 * (&1 / &3 - x)`; `&0 < &7 - &50 * x + &107 * x pow 2 - &50 * x pow 3`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: large_x_dot (private) *)
let C983LFL_LARGE_X_DOT = prove
 (`forall l h d t x z. &0 < l /\ &0 < h /\ &0 < d /\ &0 < t /\
     l pow 2 + h pow 2 = &1 /\ d pow 2 + t pow 2 = &1 /\ h <= l /\
     &1 / &5 <= x /\ x < z /\
     l = (&1 - x pow 2) / (&1 + x pow 2) /\ h = &2 * x / (&1 + x pow 2) /\
     d = (&1 - z pow 2) / (&1 + z pow 2) /\ t = &2 * z / (&1 + z pow 2) /\
     &3 * t < &2 * d
     ==> &49 / &50 < l * d + h * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C983LFL_DEN) THEN MP_TAC(SPEC `z:real` C983LFL_DEN) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(l * t - h * d) * ((&1 + x pow 2) * (&1 + z pow 2)) =
                &2 * (z - x) * (&1 + x * z) /\
                (&12 * h - &5 * l) * (&1 + x pow 2) = (&5 * x - &1) * (x + &5)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(fun th ->
      if concl th = t then SUBST1_TAC th else NO_TAC))
     [`l = (&1 - x pow 2) / (&1 + x pow 2)`; `h = &2 * x / (&1 + x pow 2)`;
      `d = (&1 - z pow 2) / (&1 + z pow 2)`; `t = &2 * z / (&1 + z pow 2)`] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < &1 + x pow 2`; `&0 < &1 + z pow 2`] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 < x`; `&0 < z`; `&0 < (&1 + x pow 2) * (&1 + z pow 2)`;
    `&0 < z - x`; `&0 < x * z`; `&0 < &2 * (z - x) * (&1 + x * z)`;
    `&0 < l * t - h * d`; `&0 <= (&5 * x - &1) * (x + &5)`; `&0 <= &12 * h - &5 * l`;
    `&0 < l * d + h * t`;
    `&0 < ((&46 * l - &9 * h) / &3) * (&2 * d - &3 * t)`;
    `&0 <= (&13 * d / &3) * (&12 * h - &5 * l)`;
    `&46 * (l * t - h * d) < &9 * (l * d + h * t)`;
    `&0 < (&9 * (l * d + h * t) - &46 * (l * t - h * d)) *
          (&9 * (l * d + h * t) + &46 * (l * t - h * d))`] THEN
  SUBGOAL_THEN `(l * d + h * t) pow 2 + (l * t - h * d) pow 2 = &1` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`l pow 2 + h pow 2 = &1`; `d pow 2 + t pow 2 = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`(&49 / &50) pow 2 < (l * d + h * t) pow 2`] THEN
  NLIN_TAC []);;

(* Lean: large_half *)
let C983LFL_LARGE_HALF = prove
 (`forall l h d t x z. &0 < l /\ &0 < h /\ &0 < d /\ &0 < t /\
     l pow 2 + h pow 2 = &1 /\ d pow 2 + t pow 2 = &1 /\ h <= l /\
     &0 < x /\ x < z /\ z < &1 / &3 /\ &2 / &7 <= z /\
     l = (&1 - x pow 2) / (&1 + x pow 2) /\ h = &2 * x / (&1 + x pow 2) /\
     d = (&1 - z pow 2) / (&1 + z pow 2) /\ t = &2 * z / (&1 + z pow 2) /\
     &83 / &100 < d /\ &3 * t < &2 * d
     ==> x * (&1 - h) < (l * d + h * t) * (&1 - d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C983LFL_DEN) THEN MP_TAC(SPEC `z:real` C983LFL_DEN) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `d <= &45 / &53` ASSUME_TAC THENL
   [UNDISCH_TAC `d = (&1 - z pow 2) / (&1 + z pow 2)` THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    NLIN_FACTS_TAC [] [`&0 <= (z - &2 / &7) * (z + &2 / &7)`] THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 < l * d`; `&0 < h * t`; `&0 < l * d + h * t`] THEN
  SUBGOAL_THEN `x * (&1 - h) = c983lfl_fv x` SUBST1_TAC THENL
   [REWRITE_TAC[C983LFL_F_DEF] THEN
    UNDISCH_TAC `h = &2 * x / (&1 + x pow 2)` THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `&0 < &1 + x pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_CASES_TAC `x <= &1 / &5` THENL
   [MP_TAC(SPEC `x:real` C983LFL_F_SMALL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `l - &1 = --x * h /\ t = z * (&1 + d)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      MAP_EVERY (fun t -> FIRST_ASSUM(fun th ->
        if concl th = t then SUBST1_TAC th else NO_TAC))
       [`l = (&1 - x pow 2) / (&1 + x pow 2)`; `h = &2 * x / (&1 + x pow 2)`;
        `d = (&1 - z pow 2) / (&1 + z pow 2)`; `t = &2 * z / (&1 + z pow 2)`] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < &1 + x pow 2`; `&0 < &1 + z pow 2`] THEN
      CONV_TAC REAL_FIELD; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 < d * (z - x)`; `&0 < t - d * x`; `&0 < h * (t - d * x)`;
      `d < l * d + h * t`;
      `(&83 / &100) * (&8 / &53) < (l * d + h * t) * (&8 / &53)`;
      `(l * d + h * t) * (&8 / &53) <= (l * d + h * t) * (&1 - d)`] THEN
    NLIN_TAC ~deg2:false [];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(SPECL [`l:real`; `h:real`; `d:real`; `t:real`; `x:real`; `z:real`]
      C983LFL_LARGE_X_DOT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPEC `x:real` C983LFL_F_UNIFORM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    NLIN_FACTS_TAC []
     [`(&49 / &50) * (&8 / &53) < (l * d + h * t) * (&8 / &53)`;
      `(l * d + h * t) * (&8 / &53) <= (l * d + h * t) * (&1 - d)`] THEN
    NLIN_TAC ~deg2:false []]);;
