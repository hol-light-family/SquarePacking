(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/StrongBarPoint.lean                *)
(* (N12Compact.CommonCases.StrongBarPoint).  The positive canonical outward  *)
(* square owns the strict point (123/50,199/100).                            *)
(*                                                                           *)
(* CanonicalScalars.bounds: CCCS_BOUNDS; OutwardScalars.increasing_          *)
(* projection / strong_bar_projection: CCOS_INCREASING_PROJECTION /          *)
(* CCOS_STRONG_BAR_PROJECTION; ClosedFrames.canonical_frame:                 *)
(* CLF_CANONICAL_FRAME; C981CompletionOutwardAnchor.nonnegative_impossible:  *)
(* C981OA_NONNEGATIVE_IMPOSSIBLE; pullY: LINSIDE_PULLY.  The translated      *)
(* square of S12.ShortCluster (q.translated 2 2) is (c, s, u - 2c - 2s,      *)
(* v + 2s - 2c, a), see CCSBP_TRANSLATED.  Lean's -1/100 is --(&1 / &100).   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_C981_OutwardAnchor.ml";;

(* Lean: S12.inside_translated_iff (source/S12/ShortCluster), at (2,2) *)
let CCSBP_TRANSLATED = prove
 (`forall c s u v a x y.
     linside c s (u - &2 * c - &2 * s) (v + &2 * s - &2 * c) a x y <=>
     linside c s u v a (x + &2) (y + &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCSBP_UNFOLD_TAC ts =
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t))) ts;;

(* a missing point gives a face inequality *)
let CCSBP_MISSING_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: positive_point *)
let CCSBP_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&1) (&13 / &50) /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&543 / &500) (&0) /\
     ~linside c s u v a (&13 / &50) (&1) /\
     ~linside c s u v a (&43 / &50) (&1) /\
     ~linside c s u v a (&543 / &500) (&1)
     ==> linside c s u v a (&23 / &50) (--(&1 / &100))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  CCSBP_UNFOLD_TAC [`linside c s u v a (&7 / &20) (&7 / &20)`;
                    `linside c s u v a (&1) (&13 / &50)`] THEN
  SUBGOAL_THEN `v < --s * &13 / &50` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (&13 / &50) (&1)` THEN
   UNDISCH_TAC `~linside c s u v a (&43 / &50) (&1)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &13 / &50 <= u` ASSUME_TAC THENL
  [CCSBP_MISSING_TAC `~linside c s u v a (&13 / &50) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `--s * &543 / &500 <= v` ASSUME_TAC THENL
  [CCSBP_MISSING_TAC `~linside c s u v a (&543 / &500) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * &543 / &500 + s` ASSUME_TAC THENL
  [CCSBP_MISSING_TAC `~linside c s u v a (&543 / &500) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `&87 / &500 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u < c * &23 / &50 + s * --(&1 / &100)` ASSUME_TAC THENL
  [ASM_CASES_TAC `u + a <= c * &43 / &50 + s` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `&2 / &5`; `&101 / &100`]
      CCOS_INCREASING_PROJECTION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
                    DISCH_TAC] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `v + a <= --s * &43 / &50 + c` ASSUME_TAC THENL
    [CCSBP_MISSING_TAC `~linside c s u v a (&43 / &50) (&1)`; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`] CCOS_STRONG_BAR_PROJECTION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    RASM_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `v < --s * &23 / &50 + c * --(&1 / &100)` ASSUME_TAC THENL
  [ASM_CASES_TAC `c <= &2 * s` THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(&3 / &5) * c + s < &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `(&16 / &25) * c - (&6 / &5) * s`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN NLIN_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `v + a <= --s * &43 / &50 + c` ASSUME_TAC THENL
   [CCSBP_MISSING_TAC `~linside c s u v a (&43 / &50) (&1)`; ALL_TAC] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: negative_corner_impossible (private) *)
let CCSBP_NEGATIVE_CORNER_IMPOSSIBLE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&3) (&3) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&143 / &50) (&3)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  CCSBP_UNFOLD_TAC [`linside c (--t) u v a (&47 / &20) (&47 / &20)`;
                    `linside c (--t) u v a (&3) (&3)`] THEN
  SUBGOAL_THEN `c * &143 / &50 + --t * &3 <= u` ASSUME_TAC THENL
  [CCSBP_MISSING_TAC `~linside c (--t) u v a (&143 / &50) (&3)`; ALL_TAC] THEN
  SUBGOAL_THEN `&51 * c < &65 * t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * &1543 / &500 + --t * &2` ASSUME_TAC THENL
  [CCSBP_MISSING_TAC `~linside c (--t) u v a (&1543 / &500) (&2)`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `&113 / &500`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
   UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: positive_point_original *)
let CCSBP_POSITIVE_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&1543 / &500) (&3) /\
     (forall z. &113 / &50 <= z /\ z <= &143 / &50 ==> ~linside c s u v a z (&3))
     ==> linside c s u v a (&123 / &50) (&199 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - &2 * c - &2 * s`; `v + &2 * s - &2 * c`; `a:real`]
    CCSBP_POSITIVE_POINT) THEN
  REWRITE_TAC[CCSBP_TRANSLATED] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: point_original *)
let CCSBP_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&3) (&113 / &50) /\
     linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&1543 / &500) (&3) /\
     (forall z. &113 / &50 <= z /\ z <= &143 / &50 ==> ~linside c s u v a z (&3))
     ==> linside c s u v a (&123 / &50) (&199 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN `u':real`
    (X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `a':real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `forall x y. linside c' s' u' v' a x y <=> linside c s u v a x y`)
           (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
    else failwith "") THEN
  ASM_CASES_TAC `&0 <= s'` THENL
  [MATCH_MP_TAC CCSBP_POSITIVE_POINT_ORIGINAL THEN ASM_REWRITE_TAC[] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  ASM_CASES_TAC `linside c' s' u' v' a (&3) (&3)` THENL
  [MATCH_MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`; `--s'`]
     CCSBP_NEGATIVE_CORNER_IMPOSSIBLE) THEN
   ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
   REPEAT CONJ_TAC THENL
   [RASM_ARITH_TAC; RASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV];
   ALL_TAC] THEN
  MATCH_MP_TAC(PURE_ONCE_REWRITE_RULE[TAUT `~p <=> p ==> false`]
    (CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (PURE_REWRITE_RULE[LINSIDE_PULLY]
    (SPECL [`c':real`; `--s'`; `u' - &4 * s'`; `&4 * c' - v' - a`; `a:real`]
      C981OA_NONNEGATIVE_IMPOSSIBLE)))) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [UNDISCH_TAC `c' * c' + s' * s' = &1` THEN REAL_ARITH_TAC;
   RASM_ARITH_TAC; RASM_ARITH_TAC;
   GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN RASM_ARITH_TAC]);;
