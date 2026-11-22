(* ========================================================================= *)
(* Port of Compact/Completion/C1092/InwardElbows.lean                        *)
(* (N12Compact.C1092InwardElbows).  The all-orientation inward-elbow         *)
(* entrance.  S12.short_projections is FSAF_SHORT_PROJECTIONS.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquareAForced.ml";;

let C1092IE_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092IE_SP_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC;;

(* contradict the negated (unfolded) membership mentioning all of pats *)
let C1092IE_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN REPEAT CONJ_TAC THEN C1092IE_LIN_TAC;;

(* Lean: positive_pair (private) *)
let C1092IE_POSITIVE_PAIR = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&1) (&803 / &500) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&803 / &500) (&1)
     ==> linside c s u v a (&2) (&87 / &50) /\ linside c s u v a (&87 / &50) (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  C1092IE_SP_TAC `&33 / &20 - &1` `&47 / &20 - &803 / &500` THEN
  C1092IE_SP_TAC `&33 / &20 - &2` `&47 / &20 - &87 / &50` THEN
  C1092IE_SP_TAC `&2 - &803 / &500` `&87 / &50 - &1` THEN
  C1092IE_SP_TAC `&1 - &803 / &500` `&87 / &50 - &1` THEN
  C1092IE_SP_TAC `&47 / &20 - &803 / &500` `&33 / &20 - &1` THEN
  C1092IE_SP_TAC `&2 - &47 / &20` `&87 / &50 - &33 / &20` THEN
  C1092IE_SP_TAC `&87 / &50 - &47 / &20` `&2 - &33 / &20` THEN
  (* d2 *)
  SUBGOAL_THEN `v < --s * &2 + c * (&87 / &50)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `u + a <= c * (&33 / &20) + s * (&47 / &20)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092IE_MISS_TAC [`s * &47 / &20`];
      C1092IE_MISS_TAC [`s * &803 / &500`]];
    ALL_TAC] THEN
  (* d1 *)
  SUBGOAL_THEN `c * &2 + s * (&87 / &50) < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `--s * (&803 / &500) + c <= v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092IE_MISS_TAC [`c * &803 / &500`];
      C1092IE_MISS_TAC [`s * &87 / &50`]];
    ALL_TAC] THEN
  (* upperV at the two targets *)
  SUBGOAL_THEN `forall x y. --s * (x - &47 / &20) + c * (y - &33 / &20) <= &1 /\
                      --s * (x - &803 / &500) + c * (y - &1) <= &1
                      ==> --s * x + c * y < v + a`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `u + a <= c * (&47 / &20) + s * (&33 / &20)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092IE_MISS_TAC [`s * &33 / &20`; `c * &47 / &20`];
      C1092IE_MISS_TAC [`c * &803 / &500`]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&2`; `&87 / &50`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&87 / &50`; `&2`]) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092IE_LIN_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092IE_LIN_TAC; DISCH_TAC] THEN
  REPEAT CONJ_TAC THEN C1092IE_LIN_TAC);;

(* Lean: swapFrame / swapFrame_inside (private) *)
let C1092IE_SWAP_INSIDE = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: pair *)
let C1092IE_PAIR = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&1) (&803 / &500) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&803 / &500) (&1) /\
     ~linside c s u v a (&87 / &50) (&1)
     ==> linside c s u v a (&2) (&87 / &50) /\ linside c s u v a (&87 / &50) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `&0 <= s'` THENL
   [MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`]
      C1092IE_POSITIVE_PAIR);
    MP_TAC(SPECL [`c':real`; `--s'`; `v':real`; `u':real`; `a':real`]
      C1092IE_POSITIVE_PAIR)] THEN
  ASM_REWRITE_TAC[C1092IE_SWAP_INSIDE] THEN
  (ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `a':real = a`))) THEN
  ASM_REWRITE_TAC[] THEN TRY C1092IE_LIN_TAC THEN
  UNDISCH_TAC `c' * c' + s' * s' = &1` THEN REAL_ARITH_TAC);;
