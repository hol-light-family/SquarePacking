(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/InnerCornerObstruction/Main.lean    *)
(* (namespace N12Compact.Completion.OtherCases.InnerCornerObstruction).     *)
(* The four-isolated-exclusion obstruction and the inner-corner corollary.  *)
(* Input: ocico_input; positive_faces / negative_impossible / reframe:      *)
(* OCICOF_*; OrdinaryBarCrosspoint.Scalars.before_half / after_half:        *)
(* OCOBCS_BEFORE_HALF / OCOBCS_AFTER_HALF; canonical_frame:                 *)
(* CLF_CANONICAL_FRAME.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_OtherCases_InnerCornerObstruction_Faces.ml";;

(* Lean: positive_four_impossible *)
let OCICOM_POSITIVE_FOUR_IMPOSSIBLE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ ocico_input c s u v a /\
      &0 < c /\ &0 <= s /\ s <= c /\
      ~linside c s u v a (&1 / &2) (&1)
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCICOF_POSITIVE_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ocico_input c s u v a` THEN REWRITE_TAC[ocico_input] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `u + a <= c / &2 + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCICOF_KEEP_TAC [`~linside c s u v a (&1 / &2) (&1)`]; ALL_TAC] THEN
  SUBGOAL_THEN `c < &2 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OCOBCS_BEFORE_HALF) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN OCICOF_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= &43 / &500 * s + c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCICOF_KEEP_TAC [`~linside c s u v a (--(&43 / &500)) (&1)`]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCOBCS_AFTER_HALF) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; OCICOF_KEEP_TAC []]);;

(* Lean: four_impossible *)
let OCICOM_FOUR_IMPOSSIBLE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ ocico_input c s u v a /\
      ~linside c s u v a (&1 / &2) (&1)
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`]
    OCICOF_INPUT_REFRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OCICOM_POSITIVE_FOUR_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OCICOF_NEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`; `--s1`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: corner_excluded *)
let OCICOM_CORNER_EXCLUDED = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&13 / &20) (&13 / &20) /\
      ~linside c s u v a (--(&43 / &500)) (&0) /\
      ~linside c s u v a (&3 / &25) (&0) /\
      ~linside c s u v a (--(&43 / &500)) (&1) /\
      ~linside c s u v a (&1 / &2) (&1)
      ==> ~linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC OCICOM_FOUR_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  ASM_REWRITE_TAC[ocico_input]);;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCICOM_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: corner_excluded_original *)
let OCICOM_CORNER_EXCLUDED_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      ~linside c s u v a (&457 / &500) (&1) /\
      ~linside c s u v a (&28 / &25) (&1) /\
      ~linside c s u v a (&457 / &500) (&2) /\
      ~linside c s u v a (&3 / &2) (&2)
      ==> ~linside c s u v a (&1) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &1 + s * &1)`; `v - (--s * &1 + c * &1)`;
                `a:real`] OCICOM_CORNER_EXCLUDED) THEN
  REWRITE_TAC[OCICOM_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
