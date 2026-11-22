(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/ShortCornerAdvance.lean             *)
(* (N12Compact.Completion.OtherCases.ShortCornerAdvance).  The exact         *)
(* shorter corner reach with (p,q,r) = (.2,.6,.22).  short_projections is   *)
(* WFP_SHORT_PROJECTIONS.  Tag OCSCA_.                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;

(* Lean: positive (private) *)
let OCSCA_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\
     s * (u + a) + c * (v + a) <= &1 /\
     linside c s u v a (&0) (&0) /\
     ~linside c s u v a (--(&3 / &5)) (&0) /\
     ~linside c s u v a (&0) (--(&1 / &5))
     ==> linside c s u v a (&11 / &50) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&1 / &5`; `&3 / &5`] WFP_SHORT_PROJECTIONS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&11 / &50`; `&1 / &5`] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c + s` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c + s <= &10 / &7` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + (&41 / &50) * c * s <= c + s` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= ((c + s) - &1) * (&10 / &7 - (c + s))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981CA_UNFOLD_TAC `linside c s u v a (&0) (&0)` THEN
  SUBGOAL_THEN `--(&3 / &5) * c <= u \/ v + a <= (&3 / &5) * s` MP_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (--(&3 / &5)) (&0)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THENL
  [SUBGOAL_THEN `v < --(&11 / &50) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= s * (u + (&3 / &5) * c) /\ &0 <= c * (v + (&11 / &50) * s) /\
                  &0 < (a - &1) * (c + s)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC;
   SUBGOAL_THEN `--(&1 / &5) * s <= u` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&0) (--(&1 / &5))` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC]);;

(* Lean: point *)
let OCSCA_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&0) /\
     ~linside c s u v a (--(&3 / &5)) (&0) /\
     ~linside c s u v a (&0) (--(&1 / &5))
     ==> linside c s u v a (&11 / &50) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) &&
     is_iff(snd(strip_forall(concl th))) then
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
     else NO_TAC) THEN
  MATCH_MP_TAC OCSCA_POSITIVE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C981CA_UPPER_WALL THEN ASM_REWRITE_TAC[]);;
