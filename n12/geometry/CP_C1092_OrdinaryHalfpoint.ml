(* ========================================================================= *)
(* Port of Compact/Completion/C1092/OrdinaryHalfpoint.lean                   *)
(* (N12Compact.C1092OrdinaryHalfpoint).  The all-angle ordinary right-hand   *)
(* central halfpoint.  S12.short_projections is FSAF_SHORT_PROJECTIONS.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquareAForced.ml";;

let C1092OH_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092OH_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN REPEAT CONJ_TAC THEN C1092OH_LIN_TAC;;

let C1092OH_SP_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC;;

(* by contradiction with the excluded point given by pats *)
let C1092OH_BY_MISS t pats =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092OH_MISS_TAC pats; ALL_TAC];;

(* Lean: canonical (private) *)
let C1092OH_CANONICAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ abs s <= c /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&3) (&87 / &50) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&3) (&2) /\
     ~linside c s u v a (&3) (&1) /\
     ~linside c s u v a (&113 / &50) (&1)
     ==> linside c s u v a (&3) (&3 / &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside; REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [C1092OH_BY_MISS `--s * &3 + c * &1 <= v` [`c * &3 + s * &1`] THEN
    C1092OH_BY_MISS `u + a <= c * &3 + s * &2` [`c * &3 + s * &2`] THEN
    C1092OH_BY_MISS `v + a <= --s * (&113 / &50) + c * &2`
      [`c * &113 / &50`; `s * &2`] THEN
    C1092OH_SP_TAC `&113 / &50 - &3` `&2 - &3 / &2` THEN
    REPEAT CONJ_TAC THEN C1092OH_LIN_TAC;
    ALL_TAC] THEN
  C1092OH_BY_MISS `v + a <= --s * &3 + c * &2` [`c * &3 + s * &2`] THEN
  SUBGOAL_THEN `v < --s * &3 + c * &1` ASSUME_TAC THENL [C1092OH_LIN_TAC; ALL_TAC] THEN
  C1092OH_BY_MISS `u + a <= c * &3 + s * &1` [`c * &3 + s * &1`] THEN
  SUBGOAL_THEN `c * &3 + s * (&3 / &2) < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092OH_SP_TAC `&3 - &113 / &50` `&3 / &2 - &2` THEN
    C1092OH_BY_MISS `v + a <= --s * (&113 / &50) + c * &2`
      [`c * &113 / &50`; `s * &2`] THEN
    SUBGOAL_THEN `u < c * (&113 / &50) + s * &1` ASSUME_TAC THENL
     [C1092OH_LIN_TAC; ALL_TAC] THEN
    C1092OH_BY_MISS `u + a <= c * (&113 / &50) + s * &1`
      [`c * &113 / &50`; `s * &1`] THEN
    C1092OH_LIN_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN C1092OH_LIN_TAC);;

(* Lean: point *)
let C1092OH_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&3) (&87 / &50) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&3) (&2) /\
     ~linside c s u v a (&3) (&1) /\
     ~linside c s u v a (&113 / &50) (&1)
     ==> linside c s u v a (&3) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] C1092OH_CANONICAL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  ASM_REWRITE_TAC[]);;
