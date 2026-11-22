(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976MergedLeft/Main.lean            *)
(* (N12Compact.Completion.OtherCases.C976MergedLeft).  C976-MERGED-LEFT-     *)
(* ENDING Theorem 1: the target point (27/100, -1/25) is owned.  Square q   *)
(* is c s u v a (unit normal and positive side explicit); Input / Profile:  *)
(* occ976ml_input / occ976ml_profile; half_large OCC976MLLF_HALF_LARGE;     *)
(* target_span OCC976MLS_TARGET_SPAN; positive_profile                      *)
(* OCC976MLP_POSITIVE_PROFILE; ClosedFrames.canonical_frame                 *)
(* CLF_CANONICAL_FRAME; Input.reframe / with_missing_target OCC976ML_INPUT_*;*)
(* C976LeftTop.UpperPoints.nonpositive_impossible                          *)
(* OCC976PG_NONPOSITIVE_IMPOSSIBLE.  Tag OCC976MLM_.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_Inputs.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_LowerFaces.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: positive_point *)
let OCC976MLM_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ occ976ml_input c s u v a /\ occ976ml_profile c s u v a
     ==> linside c s u v a (&27 / &100) (--(&1 / &25))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCC976MLLF_HALF_LARGE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCC976MLS_TARGET_SPAN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[occ976ml_input; occ976ml_profile]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (--(&43 / &500)) (&0)`;
    `linside c s u v a (&13 / &20) (&7 / &20)`] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: point *)
let OCC976MLM_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ occ976ml_input c s u v a
     ==> linside c s u v a (&27 / &100) (--(&1 / &25))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL CLF_CANONICAL_FRAME) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`]
               OCC976ML_INPUT_REFRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
  [MATCH_MP_TAC OCC976MLM_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC OCC976MLP_POSITIVE_PROFILE THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`]
                OCC976ML_INPUT_WITH_MISSING_TARGET) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`; `--sr`]
                OCC976PG_NONPOSITIVE_IMPOSSIBLE) THEN
   ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;
