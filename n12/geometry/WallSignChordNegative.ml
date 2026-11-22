(* ========================================================================= *)
(* Port of Compact/Geometry/WallSignChordNegative.lean                       *)
(* (N12Compact.WallSignChord.negative_point).  The negative canonical        *)
(* orientation; the square's sine is s = --t (Lean: q.s = -s).               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallSignChordScalars.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: negative_point *)
let WSCN_NEGATIVE_POINT = prove
 (`forall c s u v a t r.
      c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 <= c /\ &0 <= t /\ t <= c /\
      a * (c + t) / &2 - &1 <= lcx c s u v a /\
      &0 <= lcy c s u v a /\
      linside c s u v a (--(&43 / &500)) (&0) /\
      ~linside c s u v a (&13 / &20) (&7 / &20) /\
      &11 / &50 <= r /\ r <= &39 / &100
      ==> linside c s u v a (&0) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&13 / &20` `--(&1 / &25)`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lcx c s u v a = c * (u + a / &2) - s * (v + a / &2) /\
                lcy c s u v a = s * (u + a / &2) + c * (v + a / &2)`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[lcx; lcy]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  MP_TAC(SPECL [`c:real`; `t:real`] WSCS_CANONICAL_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < c /\ &0 < r` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `r:real`] WSCS_WALL_GAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] WSCS_QUADRATIC_MARGIN_TRANSPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; REAL_POW_2; REAL_MUL_RZERO; REAL_ADD_LID;
    REAL_MUL_LZERO; REAL_ADD_RID; REAL_NEG_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG]) THEN
  REWRITE_TAC[linside; REAL_MUL_RZERO; REAL_ADD_LID; REAL_MUL_LZERO; REAL_ADD_RID;
    REAL_NEG_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  SUBGOAL_THEN `t * t + c * c = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v < c * r` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 < c * r`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * r < v + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= t * (lcx c (--t) u v a - (a * (c + t) / &2 - &1))`;
      `&0 <= c * lcy c (--t) u v a`;
      `&0 < (a - &1) * (&1 + t * (c + t))`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(t * r) < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `r * t < &43 / &500 * c` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= t * (--(t * &43 / &500) - v)`;
      `&0 <= c * (--(t * r) - (u + a))`;
      `a * c <= &1 - &43 / &500 * t * t - r * c * t`] THEN
    ASM_CASES_TAC `t = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID;
        REAL_ADD_RID; REAL_SUB_RZERO]) THEN
      NLIN_TAC [];
      SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`c:real`; `t:real`; `r:real`] WSCS_NEGATIVE_U_MARGIN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
      NLIN_FACTS_TAC [] [`&0 < (a - &1) * c`] THEN
      NLIN_TAC ~deg2:false []];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `u < c * &13 / &20 + --(t * &7 / &20)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v < t * &13 / &20 + c * &7 / &20` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &13 / &20 + --(t * &7 / &20) < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 <= t * (&39 / &100 - r)`] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= t * &13 / &20 + c * &7 / &20` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      can (find_term ((=) `&13 / &20`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= t * (u - --(t * r))`;
    `&0 <= c * ((t * &13 / &20 + c * &7 / &20) - (v + a))`;
    `&0 < (a - &1) * (c + t)`; `&0 <= (t * t) * (&39 / &100 - r)`] THEN
  NLIN_TAC ~deg2:false []);;
