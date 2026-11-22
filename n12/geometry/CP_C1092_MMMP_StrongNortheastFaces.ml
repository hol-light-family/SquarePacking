(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/StrongNortheastFaces.lean           *)
(* (namespace N12Compact.C1092MMMPStrongNortheastFaces).  The northeast     *)
(* profile from its actual sign, top origin and right bar.                  *)
(* C1092MMMPEnding.Profile: c1092mend_profile; TopOnlyLeftPoint.            *)
(* positive_faces / bar_face: OCTOLP_POSITIVE_FACES / OCTOLP_BAR_FACE;      *)
(* SharpPointScalars.half_lower: OCSPS_HALF_LOWER; Normal: c977cc_normal.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_Ending.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyLeftPoint.ml";;

(* Lean: profile *)
let C1092MSNF_PROFILE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ c977cc_normal c s /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&2 / &5) /\
      ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&1) (&1) /\
      (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
      ==> c1092mend_profile c s u v a /\ &252 / &373 <= s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    is_conj(concl th) && not(can (find_term ((=) `linside`)) (concl th))))) THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  OCTOLP_SPEC_TAC [`&13 / &50`] THEN
  MP_TAC(SPEC_ALL OCTOLP_POSITIVE_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCTOLP_BAR_FACE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OCTOLP_STEP `&2 / &5 * s <= u` [`~linside c s u v a (&0) (&2 / &5)`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&11 / &25`] OCSPS_HALF_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[C1092WPS_half] THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 - &11 / &25 < (&1 + &11 / &25) * x <=> &7 / &18 < x`] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&252 / &373 <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (&275 / &373 - c) * (&275 / &373 + c) /\
                  &0 < (&252 / &373 - s) * (&252 / &373 + s)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092mend_profile] THEN ASM_REAL_ARITH_TAC);;
