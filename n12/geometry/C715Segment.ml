(* ========================================================================= *)
(* Port of Compact/Geometry/C715Segment.lean (N12Compact.C715Segment).       *)
(* The continuous two-lower-points / upper-segment obstruction for C715.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

let C715S_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[linside; lclosed; REAL_ABS_BOUNDS] THEN REAL_ARITH_TAC;;

let C715S_DIV_LT = prove
 (`forall x y p q. &0 < p /\ &0 < q ==> (x / p < y / q <=> x * q < y * p)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `y / q * p = (y * p) / q`] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ]);;

(* Lean: common_interval (private) *)
let C715S_COMMON_INTERVAL = prove
 (`forall a b c d e f.
      a < d /\ a < e /\ a < f /\ b < d /\ b < e /\ b < f /\ c < d /\ c < e /\ c < f
      ==> exists x. a < x /\ b < x /\ c < x /\ x < d /\ x < e /\ x < f`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(max a (max b c) + min d (min e f)) / &2` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: normal_margins (private) *)
let C715S_NORMAL_MARGINS = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1
         ==> c <= &1 /\ &1 <= c + t /\ &1 <= c + t - &3 / &5 * c * t /\
             &1 <= c + &3 / &5 * t * (c + t) /\ &1 <= c + &13 / &20 * t * (c + t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`; SQ_NONNEG `c - t`; SQ_NONNEG `c - &1`]
   [`c <= &1`; `t <= &1`; `&0 <= c * t`; `&1 <= c + t`; `c + t <= &3 / &2`;
    `&0 <= (&3 / &2 - (c + t)) * ((c + t) - &1)`;
    `&1 + &4 / &5 * c * t <= c + t`;
    `&0 <= t * (&1 + c - &2 * t)`; `&0 <= (&1 + c) * (c + t / &2 - &1)`;
    `&1 <= c + t / &2`; `&0 <= t * (c + t - &1)`] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: positive_segment_bound (private) *)
let C715S_POSITIVE_SEGMENT_BOUND = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&47 / &20) (&13 / &20) /\
      linside c s u v a (&3) (&3 / &5) /\
      (forall x. &12 / &5 <= x /\ x <= &3 ==> ~linside c s u v a x (&1))
      ==> s * (u + a) + c * (v + a) <= &1 \/ v + a <= c - &3 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [SUBGOAL_THEN `c = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC [];
      ALL_TAC] THEN
    DISJ1_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&3`) THEN
    UNDISCH_TAC `linside c s u v a (&3) (&3 / &5)` THEN
    ASM_REWRITE_TAC[linside] THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  SUBGOAL_THEN `s * u + c * v < &1` ASSUME_TAC THENL
   [NLIN_FACTS_TAC []
     [`s * u < s * (c * &3 + s * &3 / &5)`;
      `c * v < c * (--s * &3 + c * &3 / &5)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&12 / &5`; `(u - s) / c`; `(c - v - a) / s`; `&3`;
                `(u + a - s) / c`; `(c - v) / s`] C715S_COMMON_INTERVAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; C715S_DIV_LT] THEN
    REPEAT CONJ_TAC THEN TRY(NLIN_TAC ~deg2:false [] THEN NO_TAC) THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` MP_TAC) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; C715S_DIV_LT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_segment_bound (private) *)
let C715S_NEGATIVE_SEGMENT_BOUND = prove
 (`forall c s u v a t.
      c * c + s * s = &1 /\ &0 < a /\ &0 < c /\ &0 < t /\ t <= c /\ s = --t /\
      linside c s u v a (&47 / &20) (&13 / &20) /\
      linside c s u v a (&3) (&3 / &5) /\
      (forall x. &12 / &5 <= x /\ x <= &3 ==> ~linside c s u v a x (&1))
      ==> --t * u + c * (v + a) <= &1 \/ v + a <= &12 / &5 * t + c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  SUBGOAL_THEN `--t * (u + a) + c * v < &1` ASSUME_TAC THENL
   [NLIN_FACTS_TAC []
     [`t * (c * &3 + --t * &3 / &5) < t * (u + a)`;
      `c * v < c * (-- --t * &3 + c * &3 / &5)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&12 / &5`; `(u + t) / c`; `(v - c) / t`; `&3`;
                `(u + a + t) / c`; `(v + a - c) / t`] C715S_COMMON_INTERVAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; C715S_DIV_LT] THEN
    REPEAT CONJ_TAC THEN TRY(NLIN_TAC ~deg2:false [] THEN NO_TAC) THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` MP_TAC) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; C715S_DIV_LT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;

(* Lean: positive_impossible (private) *)
let C715S_POSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&47 / &20) (&13 / &20) /\
      linside c s u v a (&3) (&3 / &5) /\
      ~linside c s u v a (&12 / &5) (&0) /\
      ~linside c s u v a (&3) (&0) /\
      (forall x. &12 / &5 <= x /\ x <= &3 ==> ~linside c s u v a x (&1))
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C715S_NORMAL_MARGINS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C715S_POSITIVE_SEGMENT_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `--(&3) * s <= v` ASSUME_TAC THENL
   [UNDISCH_THEN `~linside c s u v a (&12 / &5) (&0)` (K ALL_TAC) THEN
    C715S_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s * (u + a) + c * (v + a) <= &1` ASSUME_TAC THENL
   [C715S_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&12 / &5 * c <= u \/ --(&12 / &5) * s <= v` MP_TAC THENL
   [UNDISCH_THEN `~linside c s u v a (&3) (&0)` (K ALL_TAC) THEN C715S_LIN_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [NLIN_FACTS_TAC []
     [`&0 <= s * (u - &12 / &5 * c)`; `&0 <= c * (v - --(&3) * s)`;
      `&0 < (a - &1) * (c + s)`] THEN
    NLIN_TAC ~deg2:false [];
    NLIN_FACTS_TAC []
     [`&0 <= s * ((u + a) - (c * &3 + s * &3 / &5))`;
      `&0 <= c * (v - --(&12 / &5) * s)`; `&0 < c * (a - &1)`] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: negative_impossible (private) *)
let C715S_NEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a t.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 < t /\ t <= c /\ s = --t /\
      linside c s u v a (&47 / &20) (&13 / &20) /\
      linside c s u v a (&3) (&3 / &5) /\
      ~linside c s u v a (&12 / &5) (&0) /\
      ~linside c s u v a (&3) (&0) /\
      (forall x. &12 / &5 <= x /\ x <= &3 ==> ~linside c s u v a x (&1))
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C715S_NORMAL_MARGINS) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`]
    C715S_NEGATIVE_SEGMENT_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  SUBGOAL_THEN `&12 / &5 * t <= v` ASSUME_TAC THENL
   [UNDISCH_THEN `~linside c (--t) u v a (&3) (&0)` (K ALL_TAC) THEN
    C715S_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--t * u + c * (v + a) <= &1` ASSUME_TAC THENL
   [C715S_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= &3 * c \/ &3 * t <= v` MP_TAC THENL
   [UNDISCH_THEN `~linside c (--t) u v a (&12 / &5) (&0)` (K ALL_TAC) THEN
    C715S_LIN_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [NLIN_FACTS_TAC []
     [`&0 <= t * (&3 * c - (u + a))`; `&0 <= c * (v - &12 / &5 * t)`;
      `&0 < (a - &1) * (c + t)`] THEN
    NLIN_TAC ~deg2:false [];
    NLIN_FACTS_TAC []
     [`&0 <= t * ((c * &47 / &20 + --t * &13 / &20) - u)`;
      `&0 <= c * (v - &3 * t)`; `&0 < c * (a - &1)`] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: lower_points_upper_segment *)
let C715S_LOWER_POINTS_UPPER_SEGMENT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&3) (&8 / &5) /\
      ~linside c s u v a (&12 / &5) (&1) /\
      ~linside c s u v a (&3) (&1) /\
      (forall x. &12 / &5 <= x /\ x <= &3 ==> ~linside c s u v a x (&2))
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall x y. linside c s (u - s) (v - c) a x y <=> linside c s u v a x (y + &1)`
    ASSUME_TAC THENL [REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - s`; `v - c`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  SUBGOAL_THEN
   `linside c1 s1 u1 v1 a (&47 / &20) (&13 / &20) /\
    linside c1 s1 u1 v1 a (&3) (&3 / &5) /\
    ~linside c1 s1 u1 v1 a (&12 / &5) (&0) /\
    ~linside c1 s1 u1 v1 a (&3) (&0) /\
    (forall x. &12 / &5 <= x /\ x <= &3 ==> ~linside c1 s1 u1 v1 a x (&1))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC C715S_POSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C715S_NEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`;
                          `--s1`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: lower_points_foreign_square *)
let C715S_LOWER_POINTS_FOREIGN_SQUARE = prove
 (`forall c s u v a cw sw uw vw aw.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&3) (&8 / &5) /\
      ~linside c s u v a (&12 / &5) (&1) /\
      ~linside c s u v a (&3) (&1) /\
      linside cw sw uw vw aw (&113 / &50) (&2) /\
      linside cw sw uw vw aw (&1543 / &500) (&2) /\
      ldisj c s u v a cw sw uw vw aw
      ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  MATCH_MP_TAC C715S_LOWER_POINTS_UPPER_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cw:real`; `sw:real`; `uw:real`; `vw:real`; `aw:real`;
                `&113 / &50`; `&2`; `&1543 / &500`; `&2`;
                `(x - &113 / &50) * &500 / &413`] CES_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall P Q. linside cw sw uw vw aw P Q ==> P = x /\ Q = &2
                      ==> linside cw sw uw vw aw x (&2)`
    (fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;
