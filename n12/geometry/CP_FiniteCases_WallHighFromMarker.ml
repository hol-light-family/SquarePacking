(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/WallHighFromMarker.lean            *)
(* S12.short_projections is WFP_SHORT_PROJECTIONS (instantiated by WFP_SP).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallLowerReach.ml";;

(* Lean: inward_point (private) *)
let FCWHM_INWARD_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&1) (&64 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&457 / &500) (&2)`; `linside c s u v a (&1) (&12 / &5)`;
    `linside c s u v a (&87 / &50) (&2)`] THEN
  MP_TAC(WFP_SP `&13 / &20` `&61 / &100`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `u + a <= c * (&33 / &20) + s * (&47 / &20)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&33 / &20) (&47 / &20)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--s + c * (&87 / &50) <= v` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&1) (&87 / &50)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: point *)
let FCWHM_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&1) (&64 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `linside c s u v a (&87 / &50) (&2)` THENL
   [ALL_TAC; MATCH_MP_TAC WLR_POINT THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  MATCH_MP_TAC FCWHM_INWARD_POINT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
