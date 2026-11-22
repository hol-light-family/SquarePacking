(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedElementary.lean               *)
(* (namespace N12Compact.Completion.OtherCases.MergedElementary).           *)
(* Elementary merged-western point comparisons.  short_projections: WFP_SP; *)
(* canonical_frame: CLF_CANONICAL_FRAME.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let OCMEL_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCMEL_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* canonical-frame reduction *)
let OCMEL_FRAME_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
    else NO_TAC));;

(* Lean: horizontal *)
let OCMEL_HORIZONTAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
      linside c s u v a (--(&7 / &20)) (&7 / &20) /\
      linside c s u v a (--(&13 / &50)) (&0) /\
      ~linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      ~linside c s u v a (&7 / &20) (&7 / &20)
      ==> linside c s u v a (--(&1 / &2)) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCMEL_FRAME_TAC THEN
  REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN `c1 * --(&1 / &2) <= u1` ASSUME_TAC THENL
   [OCMEL_LIN_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MP_TAC(INST [`c1:real`,`c:real`; `s1:real`,`s:real`] (WFP_SP `&17 / &20` `&7 / &20`));
    MP_TAC(INST [`c1:real`,`c:real`; `s1:real`,`s:real`]
      (WFP_SP `&17 / &20` `--(&7 / &20)`))] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN OCMEL_LIN_TAC);;

(* Lean: two_inward_center *)
let OCMEL_TWO_INWARD_CENTER = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
      linside c s u v a (--(&7 / &20)) (&7 / &20) /\
      linside c s u v a (--(&13 / &50)) (&0) /\
      linside c s u v a (&0) (--(&13 / &50)) /\
      linside c s u v a (&0) (&13 / &50)
      ==> linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCMEL_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s1` THEN OCMEL_LIN_TAC);;

(* Lean: horizontal_original *)
let OCMEL_HORIZONTAL_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      linside c s u v a (&87 / &50) (&2) /\
      ~linside c s u v a (&47 / &20) (&33 / &20) /\
      ~linside c s u v a (&47 / &20) (&47 / &20)
      ==> linside c s u v a (&3 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCMEL_HORIZONTAL) THEN
  REWRITE_TAC[OCMEL_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: two_inward_center_original *)
let OCMEL_TWO_INWARD_CENTER_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      linside c s u v a (&87 / &50) (&2) /\
      linside c s u v a (&2) (&87 / &50) /\
      linside c s u v a (&2) (&113 / &50)
      ==> linside c s u v a (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCMEL_TWO_INWARD_CENTER) THEN
  REWRITE_TAC[OCMEL_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
