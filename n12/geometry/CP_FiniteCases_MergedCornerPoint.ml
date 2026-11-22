(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/MergedCornerPoint.lean             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let FCMCP_UNFOLD_TAC ts =
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t))) ts;;

(* Lean: positive (private) *)
let FCMCP_POSITIVE = prove
 (`forall c s u v a.
     &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&457 / &500) (&3) /\
     linside c s u v a (&1) (&1543 / &500) /\
     linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&1) (&1457 / &500)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: negative (private) *)
let FCMCP_NEGATIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < c /\ s <= &0 /\ --s <= c /\ &1 < a /\
     linside c s u v a (&457 / &500) (&3) /\
     linside c s u v a (&1) (&1543 / &500) /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&2) (&1543 / &500)
     ==> linside c s u v a (&1) (&1457 / &500)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FCMCP_UNFOLD_TAC [`linside c s u v a (&457 / &500) (&3)`;
    `linside c s u v a (&1) (&1543 / &500)`; `linside c s u v a (&33 / &20) (&47 / &20)`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c + s:real`; SQ_NONNEG `c - s - &3 / &2`]
    [`c - s <= &3 / &2`; `--s + (&43 / &250) * c <= &1`] THEN
  SUBGOAL_THEN `v < --s + c * (&1457 / &500)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&2) (&1543 / &500)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: upper_left *)
let FCMCP_UPPER_LEFT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&457 / &500) (&3) /\
     linside c s u v a (&1) (&1543 / &500) /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&2) (&1543 / &500)
     ==> linside c s u v a (&1) (&1457 / &500)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC FCMCP_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FCMCP_NEGATIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
