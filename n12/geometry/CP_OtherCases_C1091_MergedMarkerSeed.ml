(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/MergedMarkerSeed.lean         *)
(* (namespace N12Compact.Completion.OtherCases.C1091.MergedMarkerSeed).     *)
(* S12.short_projections is WFP_SHORT_PROJECTIONS (instantiated by WFP_SP); *)
(* ClosedFrames.canonical_frame is CLF_CANONICAL_FRAME.  The OpenSquare     *)
(* invariants are explicit hypotheses c * c + s * s = &1, &0 < a.           *)
(* q.translated 1 1 is (c, s, u - (c + s), v - (--s + c), a).               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: Input (structure) *)
let c1091mms_input = new_definition
 `c1091mms_input c s u v a <=>
    &1 < a /\
    linside c s u v a (--(&43 / &500)) (&0) /\
    linside c s u v a (&13 / &20) (&13 / &20) /\
    ~linside c s u v a (&0) (&0) /\
    ~linside c s u v a (&37 / &50) (&1)`;;

(* Lean: Input.reframe *)
let C1091MMS_INPUT_REFRAME = prove
 (`forall c s u v a c' s' u' v' a'.
     c1091mms_input c s u v a /\ a' = a /\
     (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)
     ==> c1091mms_input c' s' u' v' a'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1091mms_input] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: nonpositive_impossible *)
let C1091MMS_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1091mms_input c s u v a /\
               &0 < c /\ s <= &0 /\ --s <= c
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1091mms_input] THEN STRIP_TAC THEN
  UNDISCH_TAC `~linside c s u v a (&0) (&0)` THEN
  MAP_EVERY UNDISCH_TAC [`linside c s u v a (--(&43 / &500)) (&0)`;
                         `linside c s u v a (&13 / &20) (&13 / &20)`] THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
  RASM_ARITH_TAC);;

(* Lean: positive_faces *)
let C1091MMS_POSITIVE_FACES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1091mms_input c s u v a /\
               &0 < c /\ &0 <= s /\ s <= c
     ==> &0 < s /\ &0 <= v /\ u + a <= (&37 / &50) * c + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&1` `&0`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c1091mms_input c s u v a` THEN
  REWRITE_TAC[c1091mms_input; linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(u < c * &0 + s * &0 /\ c * &0 + s * &0 < u + a /\
                   v < --s * &0 + c * &0 /\ --s * &0 + c * &0 < v + a)` THEN
    REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(u < c * &37 / &50 + s * &1 /\ c * &37 / &50 + s * &1 < u + a /\
                 v < --s * &37 / &50 + c * &1 /\ --s * &37 / &50 + c * &1 < v + a)` THEN
  REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: positive_point *)
let C1091MMS_POSITIVE_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1091mms_input c s u v a /\
               &0 < c /\ &0 <= s /\ s <= c
     ==> linside c s u v a (--(&6 / &25)) (&87 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1091MMS_POSITIVE_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&49 / &50` `&13 / &100`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `--(&6 / &25)` `&87 / &100`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c1091mms_input c s u v a` THEN
  REWRITE_TAC[c1091mms_input; linside] THEN STRIP_TAC THEN
  RASM_ARITH_TAC);;

(* Lean: point *)
let C1091MMS_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1091mms_input c s u v a
     ==> linside c s u v a (--(&6 / &25)) (&87 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] C1091MMS_INPUT_REFRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC C1091MMS_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`]
      C1091MMS_NONPOSITIVE_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* S12 translation of a square (inside_translated_iff) *)
let C1091MMS_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: point_original *)
let C1091MMS_POINT_ORIGINAL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&457 / &500) (&1) /\ linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&1) (&1) /\ ~linside c s u v a (&87 / &50) (&2)
     ==> linside c s u v a (&19 / &25) (&187 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &1 + s * &1)`; `v - (--s * &1 + c * &1)`;
                `a:real`] C1091MMS_POINT) THEN
  ASM_REWRITE_TAC[c1091mms_input; C1091MMS_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;
