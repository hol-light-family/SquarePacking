(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/F4PointTransfers.lean               *)
(* (namespace N12Compact.Completion.OtherCases.F4PointTransfers).            *)
(* Both exact F4 point transfers.  short_projections: WFP_SP;               *)
(* canonical_frame: CLF_CANONICAL_FRAME.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let OCF4PT_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCF4PT_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* canonical-frame reduction used by impossible and point *)
let OCF4PT_FRAME_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
    else NO_TAC));;

(* Lean: horizontal_positive (private) *)
let OCF4PT_HORIZONTAL_POSITIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50))
      ==> linside c s u v a (&1 / &2) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCF4PT_LIN_TAC);;

(* Lean: horizontal_negative (private) *)
let OCF4PT_HORIZONTAL_NEGATIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&0) (--(&13 / &50)) /\
      ~linside c s u v a (&1 / &2) (--(&1))
      ==> linside c s u v a (&1 / &2) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REFUTE_THEN ASSUME_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  MP_TAC(WFP_SP `&13 / &50` `--(&1 / &2)`) THEN MP_TAC(WFP_SP `&1 / &2` `--(&37 / &50)`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v + a <= --s * (&1 / &2)` ASSUME_TAC THENL [OCF4PT_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * --(&13 / &50) <= u` ASSUME_TAC THENL [OCF4PT_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * (&1 / &2) - s` ASSUME_TAC THENL [OCF4PT_LIN_TAC; ALL_TAC] THEN
  OCF4PT_LIN_TAC);;

(* Lean: horizontal *)
let OCF4PT_HORIZONTAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&0) (--(&13 / &50)) /\
      ~linside c s u v a (&1 / &2) (--(&1))
      ==> linside c s u v a (&1 / &2) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCF4PT_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OCF4PT_HORIZONTAL_POSITIVE; MATCH_MP_TAC OCF4PT_HORIZONTAL_NEGATIVE] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: upper_positive (private) *)
let OCF4PT_UPPER_POSITIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      linside c s u v a (&0) (&13 / &50)
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCF4PT_LIN_TAC);;

(* Lean: upper_negative (private) *)
let OCF4PT_UPPER_NEGATIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      linside c s u v a (&0) (&13 / &50) /\
      ~linside c s u v a (&0) (--(&13 / &50))
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&21 / &40` `&77 / &200`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c * --(&13 / &50) <= v` ASSUME_TAC THENL [OCF4PT_LIN_TAC; ALL_TAC] THEN
  OCF4PT_LIN_TAC);;

(* Lean: upper *)
let OCF4PT_UPPER = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      linside c s u v a (&0) (&13 / &50) /\
      ~linside c s u v a (&0) (--(&13 / &50))
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCF4PT_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OCF4PT_UPPER_POSITIVE; MATCH_MP_TAC OCF4PT_UPPER_NEGATIVE] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: horizontal_original *)
let OCF4PT_HORIZONTAL_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&113 / &50) (&2) /\
      linside c s u v a (&3) (&87 / &50) /\
      ~linside c s u v a (&2) (&87 / &50) /\
      ~linside c s u v a (&5 / &2) (&1)
      ==> linside c s u v a (&5 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCF4PT_HORIZONTAL) THEN
  REWRITE_TAC[OCF4PT_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: upper_original *)
let OCF4PT_UPPER_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&113 / &50) (&2) /\
      linside c s u v a (&3) (&87 / &50) /\
      linside c s u v a (&2) (&113 / &50) /\
      ~linside c s u v a (&2) (&87 / &50)
      ==> linside c s u v a (&101 / &40) (&17 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCF4PT_UPPER) THEN
  REWRITE_TAC[OCF4PT_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
