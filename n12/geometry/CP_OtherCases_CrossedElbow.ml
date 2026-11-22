(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/CrossedElbow.lean                   *)
(* (namespace N12Compact.Completion.OtherCases.CrossedElbow).                *)
(* ELBOW-CROSSPOINT.md, Theorems 2 and 3.  short_projections: WFP_SP;       *)
(* canonical_frame: CLF_CANONICAL_FRAME.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let OCCE_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCCE_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* canonical-frame reduction used by impossible and point *)
let OCCE_FRAME_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
    else NO_TAC));;

(* Lean: positive_crosspoint (private) *)
let OCCE_POSITIVE_CROSSPOINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50))
      ==> linside c s u v a (&1 / &2) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCCE_LIN_TAC);;

(* Lean: negative_impossible (private) *)
let OCCE_NEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a w.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &1 / &2 <= w /\ w <= &4 / &5 /\
      &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&1 / &2) (&0) /\
      ~linside c s u v a (&0) (--(&1 / &2)) /\
      ~linside c s u v a w (--(&1))
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  MP_TAC(WFP_SP `&1 / &2` `&1 / &2`) THEN MP_TAC(WFP_SP `&4 / &5` `--(&1 / &2)`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (w - &7 / &20) * c /\ w * --s <= (&4 / &5) * --s /\
                &0 <= (w - &1 / &2) * --s /\ w * c <= (&4 / &5) * c`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s / &2` ASSUME_TAC THENL [OCCE_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&25 * --s < &13 * c` ASSUME_TAC THENL [OCCE_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--s / &2 <= u` ASSUME_TAC THENL [OCCE_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * w - s` ASSUME_TAC THENL [OCCE_LIN_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: impossible *)
let OCCE_IMPOSSIBLE = prove
 (`forall c s u v a w.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &1 / &2 <= w /\ w <= &4 / &5 /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&1 / &2) (&0) /\
      ~linside c s u v a (&0) (--(&1 / &2)) /\
      ~linside c s u v a w (--(&1))
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCCE_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`]
      OCCE_POSITIVE_CROSSPOINT) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OCCE_NEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`;
                          `w:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: positive_point (private) *)
let OCCE_POSITIVE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      linside c s u v a (&0) (&13 / &50)
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCCE_LIN_TAC);;

(* Lean: negative_point (private) *)
let OCCE_NEGATIVE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      linside c s u v a (&0) (&13 / &50) /\
      ~linside c s u v a (&0) (--(&1 / &2))
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&21 / &40` `&5 / &8`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--c / &2 <= v` ASSUME_TAC THENL [OCCE_LIN_TAC; ALL_TAC] THEN
  OCCE_LIN_TAC);;

(* Lean: point *)
let OCCE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      linside c s u v a (&0) (&13 / &50) /\
      ~linside c s u v a (&0) (--(&1 / &2))
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCCE_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OCCE_POSITIVE_POINT; MATCH_MP_TAC OCCE_NEGATIVE_POINT] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: impossible_original *)
let OCCE_IMPOSSIBLE_ORIGINAL = prove
 (`forall c s u v a w.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &1 / &2 <= w /\ w <= &4 / &5 /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&113 / &50) (&2) /\
      linside c s u v a (&3) (&87 / &50) /\
      ~linside c s u v a (&5 / &2) (&2) /\
      ~linside c s u v a (&2) (&3 / &2) /\
      ~linside c s u v a (&2 + w) (&1)
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`; `w:real`] OCCE_IMPOSSIBLE) THEN
  REWRITE_TAC[OCCE_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(* Lean: point_original *)
let OCCE_POINT_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&113 / &50) (&2) /\
      linside c s u v a (&3) (&87 / &50) /\
      linside c s u v a (&2) (&113 / &50) /\
      ~linside c s u v a (&2) (&3 / &2)
      ==> linside c s u v a (&101 / &40) (&17 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCCE_POINT) THEN
  REWRITE_TAC[OCCE_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
