(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/TopOnlyQuadrantProfile.lean         *)
(* (N12Compact.Completion.OtherCases.TopOnlyQuadrantProfile).  The complete  *)
(* top-only entrance has one downward-quadrant support profile.  Square q is *)
(* c s u v a; the structure Data is the predicate octoqp_data.  Lean's       *)
(* turnFrame^3 r is the explicit square (sr, --cr, --vr - a, ur, a).         *)
(* canonical_frame is CLF_CANONICAL_FRAME; TopOnlyLeftPoint lemmas are       *)
(* OCTOLP_*.  Tag OCTOQP_.                                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyLeftPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: Data (structure) *)
let octoqp_data = new_definition
 `octoqp_data c s u v a <=>
    &0 < c /\ s < &0 /\ s <= u /\ (&13 / &50) * c <= v /\
    u + a <= c + (&14 / &25) * s /\ v + a <= c - s`;;

(* Lean: frame *)
let OCTOQP_FRAME = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&13 / &50) (&1) /\
     linside c s u v a (&21 / &40) (&1 / &8) /\
     ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1) /\
     ~linside c s u v a (&1) (&1) /\
     (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           octoqp_data c' s' u' v' a'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cr:real` (X_CHOOSE_THEN `sr:real` (X_CHOOSE_THEN `ur:real`
    (X_CHOOSE_THEN `vr:real` (X_CHOOSE_THEN `ar:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ar:real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) &&
     is_iff(snd(strip_forall(concl th))) then
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`] OCTOLP_POSITIVE_FACES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `&13 / &50` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];
      STRIP_TAC] THEN
    MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`] OCTOLP_BAR_FACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `cr <= &1` ASSUME_TAC THENL
     [NLIN_TAC [SQ_NONNEG `sr:real`; SQ_NONNEG `cr - &1`]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`sr:real`; `--cr`; `--vr - a`; `ur:real`; `a:real`] THEN
    REWRITE_TAC[octoqp_data] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`] OCTOLP_NEGATIVE_FACES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`] THEN
    ASM_REWRITE_TAC[octoqp_data] THEN ASM_REAL_ARITH_TAC]);;
