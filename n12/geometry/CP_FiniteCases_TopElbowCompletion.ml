(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/TopElbowCompletion.lean            *)
(* S12.short_projections is WFP_SHORT_PROJECTIONS (instantiated by WFP_SP).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: positive (private) *)
let FCTEC_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&12 / &5) (&3) /\
     linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&2) (&12 / &5) /\ ~linside c s u v a (&3) (&12 / &5)
     ==> linside c s u v a (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&47 / &20) (&47 / &20)`; `linside c s u v a (&12 / &5) (&3)`;
    `linside c s u v a (&113 / &50) (&2)`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  SUBGOAL_THEN `&2 * c + (&12 / &5) * s <= u` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&2) (&12 / &5)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&3) * s + (&12 / &5) * c <= v` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&3) (&12 / &5)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(WFP_SP `--(&37 / &50)` `&3 / &5`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: nonpositive (private) *)
let FCTEC_NONPOSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&12 / &5) (&3) /\
     linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&3) (&12 / &5)
     ==> linside c s u v a (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&47 / &20) (&47 / &20)`; `linside c s u v a (&12 / &5) (&3)`;
    `linside c s u v a (&113 / &50) (&2)`] THEN
  SUBGOAL_THEN `u + a <= &3 * c + (&12 / &5) * s` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&3) (&12 / &5)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(WFP_SP `&37 / &50` `--(&3 / &5)`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: point *)
let FCTEC_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&12 / &5) (&3) /\
     linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&2) (&12 / &5) /\ ~linside c s u v a (&3) (&12 / &5)
     ==> linside c s u v a (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC FCTEC_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FCTEC_NONPOSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
