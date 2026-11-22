(* ========================================================================= *)
(* Port of Compact/Geometry/ScalarSATGeneral.lean (N12Compact.SATGeneral).   *)
(* Separating-axis overlap for squares with independent half-sides a, b.    *)
(* (Needed by source/S12/SquareAxes; not yet present in p2.)                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ScalarSATIntervals.ml";;

(* Lean: Overlap *)
let ssg_overlap = new_definition
 `ssg_overlap a b c s U V <=>
    exists x y:real. abs x < a /\ abs y < a /\
               abs(c * x + s * y - U) < b /\ abs(--s * x + c * y - V) < b`;;

(* Lean: interval_overlap *)
let SSG_INTERVAL_OVERLAP = prove
 (`forall a b X. &0 < a /\ &0 < b /\ abs X < a + b ==> exists x. abs x < a /\ abs(x - X) < b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SSI_ABS_LT] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--a:real`; `X - b:real`; `X - b:real`; `a:real`; `X + b:real`; `X + b:real`]
    SSI_BETWEEN_THREE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `x:real` THEN ASM_REAL_ARITH_TAC);;

(* Lean: positive_y_intervals *)
let SSG_POSITIVE_Y_INTERVALS = prove
 (`forall a b c s X Y U V.
     &0 < a /\ &0 < b /\ &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < a + b * (c + s) /\ abs Y < a + b * (c + s) /\
     abs U < b + a * (c + s) /\ abs V < b + a * (c + s)
     ==> exists y. (--a < y /\ (U - b - c * a) / s < y /\ (V - b - s * a) / c < y /\
              Y - b * (c + s) < y) /\
             (y < a /\ y < (U + b + c * a) / s /\ y < (V + b + s * a) / c /\
              y < Y + b * (c + s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SSI_ABS_LT; REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c * U - s * V = X /\ s * U + c * V = Y /\
                a * (c * c + s * s) = a /\ b * (c * c + s * s) = b` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * a /\ &0 < s * a` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC SSI_BETWEEN_FOUR THEN
  SIMP_TAC[SSI_DIV_LT_DIV; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s:real`]);;

(* Lean: positive_overlap *)
let SSG_POSITIVE_OVERLAP = prove
 (`forall a b c s X Y U V.
     &0 < a /\ &0 < b /\ &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < a + b * (c + s) /\ abs Y < a + b * (c + s) /\
     abs U < b + a * (c + s) /\ abs V < b + a * (c + s)
     ==> ssg_overlap a b c s U V`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SSG_POSITIVE_Y_INTERVALS) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s * U + c * V = Y /\ y * (c * c + s * s) = y` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `exists x. (--a < x /\ (U - b - s * y) / c < x /\ (c * y - V - b) / s < x) /\
        (x < a /\ x < (U + b - s * y) / c /\ x < (c * y - V + b) / s)`
  MP_TAC THENL
   [MATCH_MP_TAC SSI_BETWEEN_THREE THEN
    SIMP_TAC[SSI_DIV_LT_DIV; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
    REPEAT CONJ_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; ASSUME `&0 < c`; ASSUME `&0 < s`] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ssg_overlap] THEN MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN
  REWRITE_TAC[SSI_ABS_LT] THEN RASM_ARITH_TAC);;

(* Lean: nonnegative_overlap *)
let SSG_NONNEGATIVE_OVERLAP = prove
 (`forall a b c s X Y U V.
     &0 < a /\ &0 < b /\ &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < a + b * (c + s) /\ abs Y < a + b * (c + s) /\
     abs U < b + a * (c + s) /\ abs V < b + a * (c + s)
     ==> ssg_overlap a b c s U V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `c = &0` THENL
   [SUBGOAL_THEN `s = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
      DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ &1 <= x ==> x = &1`) THEN
      CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `X:real`] SSG_INTERVAL_OVERLAP) THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `Y:real`] SSG_INTERVAL_OVERLAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC)] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC)] THEN
    REWRITE_TAC[ssg_overlap] THEN MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL
   [SUBGOAL_THEN `c = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
      DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ &1 <= x ==> x = &1`) THEN
      CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `X:real`] SSG_INTERVAL_OVERLAP) THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `Y:real`] SSG_INTERVAL_OVERLAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC)] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC)] THEN
    REWRITE_TAC[ssg_overlap] THEN MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SSG_POSITIVE_OVERLAP THEN
  MAP_EVERY EXISTS_TAC [`X:real`; `Y:real`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: flip_s *)
let SSG_FLIP_S = prove
 (`forall a b c s U V. ssg_overlap a b c (--s) U (--V) ==> ssg_overlap a b c s U V`,
  REWRITE_TAC[ssg_overlap] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `--y:real`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: flip_c *)
let SSG_FLIP_C = prove
 (`forall a b c s U V. ssg_overlap a b (--c) s U (--V) ==> ssg_overlap a b c s U V`,
  REWRITE_TAC[ssg_overlap] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`--x:real`; `y:real`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: nonneg_c_overlap *)
let SSG_NONNEG_C_OVERLAP = prove
 (`forall a b c s X Y U V.
     &0 < a /\ &0 < b /\ &0 <= c /\ c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < a + b * (abs c + abs s) /\ abs Y < a + b * (abs c + abs s) /\
     abs U < b + a * (abs c + abs s) /\ abs V < b + a * (abs c + abs s)
     ==> ssg_overlap a b c s U V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 <= s` THENL
   [MATCH_MP_TAC SSG_NONNEGATIVE_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`X:real`; `Y:real`] THEN
    SUBGOAL_THEN `abs c = c /\ abs s = s` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `abs c = c`; ASSUME `abs s = s`]) THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC SSG_FLIP_S THEN MATCH_MP_TAC SSG_NONNEGATIVE_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`X:real`; `--Y:real`] THEN
    SUBGOAL_THEN `abs c = c /\ abs s = --s` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `abs c = c`; ASSUME `abs s = --s`]) THEN
    REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]]);;

(* Lean: overlap *)
let SSG_OVERLAP = prove
 (`forall a b c s X Y U V.
     &0 < a /\ &0 < b /\ c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < a + b * (abs c + abs s) /\ abs Y < a + b * (abs c + abs s) /\
     abs U < b + a * (abs c + abs s) /\ abs V < b + a * (abs c + abs s)
     ==> ssg_overlap a b c s U V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 <= c` THENL
   [MATCH_MP_TAC SSG_NONNEG_C_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`X:real`; `Y:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SSG_FLIP_C THEN MATCH_MP_TAC SSG_NONNEG_C_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`--X:real`; `Y:real`] THEN
    REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_ABS_NEG] THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]]);;
