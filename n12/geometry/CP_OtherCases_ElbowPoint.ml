(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/ElbowPoint.lean                     *)
(* (N12Compact.Completion.OtherCases.ElbowPoint).  The three-anchor elbow    *)
(* transfer, with all signed canonical orientations.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let OCEP_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[linside; lclosed; REAL_ABS_BOUNDS] THEN REAL_ARITH_TAC;;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCEP_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_impossible *)
let OCEP_POSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&7 / &20) (&7 / &20) /\
      ~linside c s u v a (&1) (--(&2 / &5))
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `--(&13 / &20)` `&3 / &4`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  OCEP_LIN_TAC);;

(* Lean: negative_faces *)
let OCEP_NEGATIVE_FACES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&7 / &20) (&7 / &20) /\
      ~linside c s u v a (&1) (--(&2 / &5)) /\
      ~linside c s u v a (&543 / &500) (&0)
      ==> u + a <= c - &2 / &5 * s /\ v + a <= &7 / &20 * (c - s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  MP_TAC(WFP_SP `&13 / &20` `--(&3 / &4)`) THEN
  MP_TAC(WFP_SP `&92 / &125` `--(&7 / &20)`) THEN
  MP_TAC(WFP_SP `&43 / &500` `&2 / &5`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v + a <= --s * &7 / &20 + c * &7 / &20` ASSUME_TAC THENL
   [OCEP_LIN_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  UNDISCH_THEN `~linside c s u v a (&7 / &20) (&7 / &20)` (K ALL_TAC) THEN
  UNDISCH_THEN `~linside c s u v a (&543 / &500) (&0)` (K ALL_TAC) THEN
  OCEP_LIN_TAC);;

(* Lean: points *)
let OCEP_POINTS = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&7 / &20) (&7 / &20) /\
      ~linside c s u v a (&1) (--(&2 / &5)) /\
      ~linside c s u v a (&543 / &500) (&0)
      ==> linside c s u v a (&0) (--(&1 / &2)) /\
          linside c s u v a (&1 / &8) (--(&21 / &40))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) then
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
      else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC OCEP_POSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`]
    OCEP_NEGATIVE_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s1:real`] [`c1 <= &1`] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `&7 / &20`; `&17 / &20`] WFP_SHORT_PROJECTIONS) THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `&9 / &40`; `&7 / &8`] WFP_SHORT_PROJECTIONS) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_neg(concl th) then ALL_TAC else NO_TAC)) THEN
  OCEP_LIN_TAC);;

(* Lean: points_original *)
let OCEP_POINTS_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&113 / &50) (&2) /\
      linside c s u v a (&3) (&87 / &50) /\
      ~linside c s u v a (&47 / &20) (&47 / &20) /\
      ~linside c s u v a (&3) (&8 / &5) /\
      ~linside c s u v a (&1543 / &500) (&2)
      ==> linside c s u v a (&2) (&3 / &2) /\
          linside c s u v a (&17 / &8) (&59 / &40)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`;
                `v - (--s * &2 + c * &2)`; `a:real`] OCEP_POINTS) THEN
  REWRITE_TAC[OCEP_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;
