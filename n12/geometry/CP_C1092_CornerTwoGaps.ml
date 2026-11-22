(* ========================================================================= *)
(* Port of Compact/Completion/C1092/CornerTwoGaps.lean                       *)
(* (N12Compact.C1092CornerTwoGaps).  The asymmetric two-short-gaps outward-  *)
(* corner obstruction.  S12.short_projections is FSAF_SHORT_PROJECTIONS.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquareAForced.ml";;

let C1092CTG_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092CTG_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092CTG_LIN_TAC; DISCH_TAC];;

let C1092CTG_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN REPEAT CONJ_TAC THEN C1092CTG_LIN_TAC;;

(* Lean: positive_impossible (private) *)
let C1092CTG_POSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a r t.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     &0 < r /\ r < &2 / &5 /\ &0 < t /\ t < &2 / &5 /\
     (&1 - r) pow 2 + (&1 - t) pow 2 <= &1 /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&12 / &5) (&3) /\
     linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&2 + r) (&3) /\
     ~linside c s u v a (&3) (&2 + t) /\
     ~linside c s u v a (&3) (&3)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  C1092CTG_LE_MUL_TAC `s:real` `&2 / &5 - t` THEN
  C1092CTG_LE_MUL_TAC `c:real` `&2 / &5 - t` THEN
  C1092CTG_LE_MUL_TAC `s:real` `t:real` THEN
  C1092CTG_LE_MUL_TAC `c:real` `&2 / &5 - r` THEN
  C1092CTG_LE_MUL_TAC `s:real` `&2 / &5 - r` THEN
  C1092CTG_LE_MUL_TAC `r:real` `c:real` THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&1 - t`; `&1 - r`] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(&1 - r) pow 2 + (&1 - t) pow 2 <= &1` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `u + a <= c * &3 + s * &3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092CTG_MISS_TAC [`c * &3 + s * &3`]; ALL_TAC] THEN
  SUBGOAL_THEN `--s * &3 + c * (&2 + t) <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092CTG_MISS_TAC [`s * (&2 + t)`]; ALL_TAC] THEN
  SUBGOAL_THEN `u < c * (&2 + r) + s * &3` ASSUME_TAC THENL
   [C1092CTG_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s * (&2 + r) + c * &3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092CTG_MISS_TAC [`c * (&2 + r)`]; ALL_TAC] THEN
  C1092CTG_LIN_TAC);;

(* Lean: swapped / swapped_inside (private) *)
let C1092CTG_SWAPPED_INSIDE = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: impossible *)
let C1092CTG_IMPOSSIBLE = prove
 (`forall c s u v a r t.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     &0 < r /\ r < &2 / &5 /\ &0 < t /\ t < &2 / &5 /\
     (&1 - r) pow 2 + (&1 - t) pow 2 <= &1 /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&12 / &5) (&3) /\
     linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&2 + r) (&3) /\
     ~linside c s u v a (&3) (&2 + t) /\
     ~linside c s u v a (&3) (&3)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  ASM_CASES_TAC `&0 <= s'` THENL
   [MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`; `r:real`; `t:real`]
      C1092CTG_POSITIVE_IMPOSSIBLE);
    MP_TAC(SPECL [`c':real`; `--s'`; `v':real`; `u':real`; `a:real`; `t:real`; `r:real`]
      C1092CTG_POSITIVE_IMPOSSIBLE)] THEN
  ASM_REWRITE_TAC[C1092CTG_SWAPPED_INSIDE] THEN
  REPEAT CONJ_TAC THEN TRY C1092CTG_LIN_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th -> is_real_rel(concl th))) THEN
  REAL_ARITH_TAC);;
