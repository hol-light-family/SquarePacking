(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/InnerCornerObstruction/Inward.lean  *)
(* (namespace N12Compact.Completion.OtherCases.InnerCornerObstruction).     *)
(* Input: ocico_input (fields side, origin, marker, missingLeft,            *)
(* missingNear, missingUpper); Faces: OCICOF_*; Scalars: OCICS_*;           *)
(* CanonicalScalars.bounds: CCCS_BOUNDS; canonical_frame:                   *)
(* CLF_CANONICAL_FRAME; inside_translated_iff: the local lemma            *)
(* OCICOI_TRANSLATED.                                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_InnerCornerObstruction_Faces.ml";;
needs "n12/geometry/CP_OtherCases_InnerCornerObstruction_Scalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let OCICOI_NEG_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;;

let OCICOI_SC_TAC th =
  MP_TAC(SPECL [`c:real`; `s:real`] th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: positive_inward_impossible *)
let OCICOI_POSITIVE_INWARD_IMPOSSIBLE = prove
 (`forall c s u v a k y. c * c + s * s = &1 /\ &0 < a /\ ocico_input c s u v a /\
     &1 / &2 <= k /\ k <= &27 / &50 /\ &101 / &100 <= y /\ y <= &26 / &25 /\
     &0 < c /\ &0 <= s /\ s <= c /\
     ~linside c s u v a (&37 / &50) (&1) /\ ~linside c s u v a k y
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OCICOF_POSITIVE_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ocico_input] o
    check (fun th -> concl th = `ocico_input c s u v a`)) THEN
  MAP_EVERY UNDISCH_TAC [`linside c s u v a (&0) (&0)`;
                         `linside c s u v a (&13 / &20) (&13 / &20)`] THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `u + a <= (&37 / &50) * c + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCICOI_NEG_TAC `~linside c s u v a (&37 / &50) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `c < &6 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCICOI_SC_TAC OCICS_BEFORE_SIXTH THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&43 / &500) * s + c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCICOI_NEG_TAC `~linside c s u v a (--(&43 / &500)) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `&9 * s < &4 * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCICOI_SC_TAC OCICS_AFTER_FOUR_NINTH THEN RASM_ARITH_TAC; ALL_TAC] THEN
  OCICOI_SC_TAC OCICS_UPPER_V THEN
  OCICOI_SC_TAC OCICS_UPPER_U THEN
  SUBGOAL_THEN `&0 < c * k /\ &0 <= s * y /\ &0 <= s * (&13 / &20 - k) /\
                &0 < c * (y - &13 / &20) /\ &0 <= c * (&26 / &25 - y) /\
                &0 <= s * (k - &1 / &2) /\ &0 <= c * (&27 / &50 - k) /\
                &0 <= s * (&26 / &25 - y)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * k + s * y` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCICOI_NEG_TAC `~linside c s u v a k y`; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: inward_impossible *)
let OCICOI_INWARD_IMPOSSIBLE = prove
 (`forall c s u v a k y. c * c + s * s = &1 /\ &0 < a /\ ocico_input c s u v a /\
     &1 / &2 <= k /\ k <= &27 / &50 /\ &101 / &100 <= y /\ y <= &26 / &25 /\
     ~linside c s u v a (&37 / &50) (&1) /\ ~linside c s u v a k y
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`] OCICOF_INPUT_REFRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`; `k:real`; `y:real`]
      OCICOI_POSITIVE_INWARD_IMPOSSIBLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`; `--s1`]
      OCICOF_NEGATIVE_IMPOSSIBLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]]);;

(* Lean: inward_corner_excluded *)
let OCICOI_INWARD_CORNER_EXCLUDED = prove
 (`forall c s u v a k y. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (--(&43 / &500)) (&0) /\
     ~linside c s u v a (&3 / &25) (&0) /\
     ~linside c s u v a (--(&43 / &500)) (&1) /\
     &1 / &2 <= k /\ k <= &27 / &50 /\ &101 / &100 <= y /\ y <= &26 / &25 /\
     ~linside c s u v a (&37 / &50) (&1) /\ ~linside c s u v a k y
     ==> ~linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL OCICOI_INWARD_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[ocico_input]);;

(* S12 translation of a square (inside_translated_iff) *)
let OCICOI_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inward_corner_excluded_original *)
let OCICOI_INWARD_CORNER_EXCLUDED_ORIGINAL = prove
 (`forall c s u v a k y. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&457 / &500) (&1) /\
     ~linside c s u v a (&28 / &25) (&1) /\
     ~linside c s u v a (&457 / &500) (&2) /\
     &1 / &2 <= k /\ k <= &27 / &50 /\ &101 / &100 <= y /\ y <= &26 / &25 /\
     ~linside c s u v a (&87 / &50) (&2) /\ ~linside c s u v a (&1 + k) (&1 + y)
     ==> ~linside c s u v a (&1) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &1 + s * &1)`; `v - (--s * &1 + c * &1)`;
                `a:real`; `k:real`; `y:real`] OCICOI_INWARD_CORNER_EXCLUDED) THEN
  REWRITE_TAC[OCICOI_TRANSLATED] THEN
  SUBGOAL_THEN `k + &1 = &1 + k /\ y + &1 = &1 + y` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;
