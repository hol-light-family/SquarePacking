(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MixedSpan.lean (N12Compact.C1092MixedSpan)*)
(* The six-point mixed-span obstruction.                                     *)
(* S12.short_projections is FSAF_SHORT_PROJECTIONS.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquareAForced.ml";;

let C1092MS_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MS_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN REPEAT CONJ_TAC THEN C1092MS_LIN_TAC;;

(* helpers: the two continuous scalar bounds of canonical_impossible *)
let C1092MS_STEEP = prove
 (`forall c s a. c * c + s * s = &1 /\ &0 <= s /\ &0 < c /\ s <= c /\ &1 < a /\
           a <= (&37 / &50) * (c + s) ==> c < &2 * s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - &2 * s) * (&2 * c - s)`; `c * s <= &2 / &5`;
    `(c + s) * (c + s) <= &9 / &5`;
    `&0 < ((&37 / &50) * (c + s) - &1) * ((&37 / &50) * (c + s) + &1)`] THEN
  NLIN_TAC []);;

let C1092MS_FINAL = prove
 (`forall c s a. c * c + s * s = &1 /\ &0 <= s /\ c < &2 * s /\ &1 < a /\
           a <= c + (&7 / &50) * s ==> false`,
  REPEAT STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= s * ((&2451 / &2500) * s - (&7 / &25) * c)`;
    `(c + (&7 / &50) * s) * (c + (&7 / &50) * s) <= &1`;
    `&0 < (c + (&7 / &50) * s - &1) * (c + (&7 / &50) * s + &1)`] THEN
  NLIN_TAC []);;

(* Lean: canonical_impossible (private) *)
let C1092MS_CANONICAL_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ abs s <= c /\
     linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&113 / &50) (&1) /\
     ~linside c s u v a (&12 / &5) (&1)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside; REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  ASM_CASES_TAC `s <= &0` THENL
   [SUBGOAL_THEN `v + a <= --s * (&113 / &50) + c * &2` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092MS_MISS_TAC [`c * &113 / &50`; `s * &2`]; ALL_TAC] THEN
    SUBGOAL_THEN `--s * (&113 / &50) + c * &1 <= v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092MS_MISS_TAC [`c * &113 / &50`; `s * &1`]; ALL_TAC] THEN
    C1092MS_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * &3 + s * (&87 / &50)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MS_MISS_TAC [`c * &3`; `s * &87 / &50`]; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s * (&113 / &50) + c * &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MS_MISS_TAC [`c * &113 / &50`; `s * &2`]; ALL_TAC] THEN
  SUBGOAL_THEN `v < --s * (&113 / &50) + c * &1` ASSUME_TAC THENL
   [C1092MS_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (&113 / &50) + s * &1 <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MS_MISS_TAC [`c * &113 / &50`; `s * &1`]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `a:real`] C1092MS_STEEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MS_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&3 - &12 / &5`; `&87 / &50 - &1`]
    FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  SUBGOAL_THEN `--s * (&12 / &5) + c * &1 <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MS_MISS_TAC [`c * &12 / &5`]; ALL_TAC] THEN
  MATCH_MP_TAC C1092MS_FINAL THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MS_LIN_TAC);;

(* Lean: impossible *)
let C1092MS_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&113 / &50) (&1) /\
     ~linside c s u v a (&12 / &5) (&1)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`]
    C1092MS_CANONICAL_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  ASM_REWRITE_TAC[]);;
