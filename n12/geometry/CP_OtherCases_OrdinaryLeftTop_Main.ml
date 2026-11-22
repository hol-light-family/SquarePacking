(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/Main.lean           *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop).            *)
(* Input: ocolti_input; Profile: oltp_profile; canonical_frame:             *)
(* CLF_CANONICAL_FRAME; positive_profile / upper_points: OLTP_*;            *)
(* nonpositive_impossible: OLTN_NONPOSITIVE_IMPOSSIBLE.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_Negative.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_Positive.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: frame *)
let OLTM_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocolti_input c s u v a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           oltp_profile c' s' u' v' a' /\
           linside c' s' u' v' a' (&7 / &25) (&1) /\
           linside c' s' u' v' a' (&2 / &5) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ocolti_input c1 s1 u1 v1 a1` ASSUME_TAC THENL
   [MATCH_MP_TAC OCOLTI_INPUT_REFRAME THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`]
      OLTP_POSITIVE_PROFILE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`]
      OLTP_UPPER_POINTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `false` CONTR_TAC THEN
    MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`; `--s1`]
      OLTN_NONPOSITIVE_IMPOSSIBLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]]);;

(* Lean: origin_of_profile *)
let OLTM_ORIGIN_OF_PROFILE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocolti_input c s u v a /\
               oltp_profile c s u v a
     ==> linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocolti_input; oltp_profile] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OLTSM_ORIGINUPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `linside c s u v a (&0) (&13 / &50)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN RASM_ARITH_TAC);;

(* Lean: origin *)
let OLTM_ORIGIN = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocolti_input c s u v a
     ==> linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OLTM_FRAME) THEN ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  MATCH_MP_TAC OLTM_ORIGIN_OF_PROFILE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OCOLTI_INPUT_REFRAME THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: impossible_with_missing_origin *)
let OLTM_IMPOSSIBLE_WITH_MISSING_ORIGIN = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocolti_input c s u v a /\
               ~linside c s u v a (&0) (&0)
     ==> false`,
  MESON_TAC[OLTM_ORIGIN]);;
