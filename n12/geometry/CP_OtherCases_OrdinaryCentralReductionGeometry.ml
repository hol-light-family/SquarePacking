(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryCentralReductionGeometry    *)
(* (N12Compact.Completion.OtherCases.OrdinaryCentralReduction).  The        *)
(* two-short-chord specialization (r=.65, heights .74,.65).                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

let OCOCRG_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[linside; lclosed; REAL_ABS_BOUNDS] THEN REAL_ARITH_TAC;;

let OCOCRG_DIV_LT = prove
 (`forall x y p q. &0 < p /\ &0 < q ==> (x / p < y / q <=> x * q < y * p)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `y / q * p = (y * p) / q`] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ]);;

(* Lean: common_interval (private) *)
let OCOCRG_COMMON_INTERVAL = prove
 (`forall a b c d e f.
      a < d /\ a < e /\ a < f /\ b < d /\ b < e /\ b < f /\ c < d /\ c < e /\ c < f
      ==> exists x. a < x /\ b < x /\ c < x /\ x < d /\ x < e /\ x < f`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(max a (max b c) + min d (min e f)) / &2` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: upper_bar (private) *)
let OCOCRG_UPPER_BAR = prove
 (`forall c s u v a h0 h1.
      c * c + s * s = &1 /\ &0 < a /\ &0 < c /\ &0 < s /\ s <= c /\
      &0 < h0 /\ h0 < &1 /\ &13 / &20 <= h1 /\ h1 < &1 /\
      linside c s u v a (&0) h0 /\ linside c s u v a (&13 / &20) h1 /\
      (forall x. &0 <= x /\ x <= &13 / &20 ==> ~linside c s u v a x (&1))
      ==> s * (u + a) + c * (v + a) <= &1 \/ v + a <= c - &13 / &20 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th)))) THEN
  NLIN_FACTS_TAC []
   [`&0 < c * (&1 - h0)`; `&0 <= s * (h1 - &13 / &20)`; `&0 < s * (&1 - h0)`;
    `s * u < s * (c * &0 + s * h0)`; `c * v < c * (--s * &0 + c * h0)`;
    `s * u + c * v < &1`] THEN
  MP_TAC(SPECL [`&0`; `(u - s) / c`; `(c - v - a) / s`; `&13 / &20`;
                `(u + a - s) / c`; `(c - v) / s`] OCOCRG_COMMON_INTERVAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; OCOCRG_DIV_LT] THEN
    REPEAT CONJ_TAC THEN TRY(NLIN_TAC ~deg2:false [] THEN NO_TAC) THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` MP_TAC) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; OCOCRG_DIV_LT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;

(* Lean: positive_impossible (private) *)
let OCOCRG_POSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a h0 h1.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      &13 / &20 <= h0 /\ h0 < &1 /\ &13 / &20 <= h1 /\ h1 < &1 /\
      linside c s u v a (&0) h0 /\ linside c s u v a (&13 / &20) h1 /\
      ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (&13 / &20) (&0) /\
      (forall x. &0 <= x /\ x <= &13 / &20 ==> ~linside c s u v a x (&1))
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL
   [SUBGOAL_THEN `c = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC [];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (is_forall o concl)) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `linside`)) (concl th)))) THEN
    ASM_REWRITE_TAC[linside] THEN
    CONV_TAC(DEPTH_CONV REAL_RAT_LE_CONV) THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_LID; REAL_NEG_0;
                REAL_ADD_LID; REAL_ADD_RID] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h0:real`; `h1:real`]
    OCOCRG_UPPER_BAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th)))) THEN
  NLIN_FACTS_TAC [] [`&0 < h0 * s`; `&0 < h0 * c`; `&0 < h1 * s`] THEN
  SUBGOAL_THEN `&13 / &20 * c <= u \/ --(&13 / &20) * s <= v` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * (u + a) + c * (v + a) <= &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o
      check (fun th -> can (find_term ((=) `&13 / &20 * c`)) (concl th))) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o
      check (fun th -> is_disj(concl th))) THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
    NLIN_FACTS_TAC [SQ_NONNEG `c - s:real`]
     [`c * u < c * (c * &0 + s * h0)`; `&0 <= c * (u - &13 / &20 * c)`;
      `s * (c * h0) < s * (v + a)`;
      `&0 <= s * ((c - &13 / &20 * s) - (v + a))`; `c * s <= &1 / &2`] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`s * (c * &13 / &20 + s * h1) < s * (u + a)`;
      `&0 <= (s * s) * (h1 - &13 / &20)`; `&0 <= c * v`; `&0 < c * (a - &1)`;
      `&0 <= &29 / &20 * c + &13 / &20 * s - &1`;
      `&0 <= s * (&29 / &20 * c + &13 / &20 * s - &1)`] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&13 / &20) * s <= v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o
      check (fun th -> can (find_term ((=) `&13 / &20 * c`)) (concl th))) THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c * c) * u + (s * s) * u = u` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `s - &1 / &2`]
     [`&0 <= (s - &1 / &2) * (s - &1 / &2)`;
      `(c * c) * u < (c * c) * (c * &0 + s * h0)`;
      `(c * s) * (c * h0) < (c * s) * (v + a)`;
      `s * (s * (u + a) + c * (v + a)) <= s * &1`;
      `&0 < (s * s) * (a - &1)`] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= s * u`; `&0 <= c * (v - --(&13 / &20) * s)`;
    `&0 < (a - &1) * (c + s)`; `&0 <= c * s`] THEN
  RASM_ARITH_TAC);;

(* Lean: mirror, mirror_inside (private) *)
let OCOCRG_MIRROR_INSIDE = prove
 (`forall c s u v a x y.
      linside c (--s) (&13 / &20 * c - u - a) (v + &13 / &20 * s) a x y <=>
      linside c s u v a (&13 / &20 - x) y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: local_impossible *)
let OCOCRG_LOCAL_IMPOSSIBLE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&0) (&37 / &50) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
      ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (&13 / &20) (&0) /\
      (forall x. &0 <= x /\ x <= &13 / &20 ==> ~linside c s u v a x (&1))
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) then
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OCOCRG_POSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`;
                          `&37 / &50`; `&13 / &20`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`c1:real`; `--s1`; `&13 / &20 * c1 - u1 - a`; `v1 + &13 / &20 * s1`;
                  `a:real`; `&13 / &20`; `&37 / &50`] OCOCRG_POSITIVE_IMPOSSIBLE) THEN
    REWRITE_TAC[OCOCRG_MIRROR_INSIDE] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th))) THEN
    ASM_REAL_ARITH_TAC]);;

(* Lean: foreign_bar_impossible *)
let OCOCRG_FOREIGN_BAR_IMPOSSIBLE = prove
 (`forall c s u v a cw sw uw vw aw.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&0) (&37 / &50) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
      ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (&13 / &20) (&0) /\
      linside cw sw uw vw aw (--(&43 / &500)) (&1) /\
      linside cw sw uw vw aw (&37 / &50) (&1) /\
      ldisj c s u v a cw sw uw vw aw
      ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  MATCH_MP_TAC OCOCRG_LOCAL_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cw:real`; `sw:real`; `uw:real`; `vw:real`; `aw:real`;
                `--(&43 / &500)`; `&1`; `&37 / &50`; `&1`;
                `&500 / &413 * (x + &43 / &500)`] CES_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall P Q. linside cw sw uw vw aw P Q ==> P = x /\ Q = &1
                      ==> linside cw sw uw vw aw x (&1)`
    (fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;
