(* ========================================================================= *)
(* Port of Compact/Geometry/MergedLeftEscapeAux.lean                         *)
(* (N12Compact.MergedLeftEscapeAux).  A center escape by the merged left     *)
(* central owner consumes a real auxiliary point.                            *)
(* pullY (S12.Symmetry) is the 5-tuple map of LINSIDE_PULLY.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/MergedLeftCornerSector.ml";;

(* Lean: transverse_margin (private) *)
let MLEA_TRANSVERSE_MARGIN = prove
 (`forall c s. c * c + s * s = &1 /\ &0 < c /\ &0 <= s /\ &2331 * s < &1300 * c
         ==> &13 / &25 * c + s <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`]
   [`&5 * s <= &3 * c`; `&0 <= c * (&3 * c - &5 * s)`;
    `(&13 / &25 * c + s) * (&13 / &25 * c + s) <= &1`] THEN
  NLIN_TAC [SQ_NONNEG `&13 / &25 * c + s - &1`]);;

(* Lean: inward *)
let MLEA_INWARD = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&2) (&2) /\
      ~linside c s u v a (&1) (&87 / &50) /\
      ~linside c s u v a (&1) (&113 / &50) /\
      ~linside c s u v a (&8 / &5) (&1)
      ==> linside c s u v a (&2) (&87 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] MLE_CENTER_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] MLCS_LOWER_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] MLCS_SECTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] MLE_UPPER_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] MLEA_TRANSVERSE_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_neg(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inward_or *)
let MLEA_INWARD_OR = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&2) (&2) /\
      ~linside c s u v a (&1) (&87 / &50) /\
      ~linside c s u v a (&1) (&113 / &50) /\
      ~linside c s u v a (&8 / &5) (&1) /\
      ~linside c s u v a (&8 / &5) (&3)
      ==> linside c s u v a (&2) (&87 / &50) \/ linside c s u v a (&2) (&113 / &50)`,
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
   [DISJ1_TAC THEN MATCH_MP_TAC MLEA_INWARD THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN
    MP_TAC(SPECL [`c1:real`; `--s1`; `u1 - &4 * s1`; `&4 * c1 - v1 - a`; `a:real`]
      MLEA_INWARD) THEN
    REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;
