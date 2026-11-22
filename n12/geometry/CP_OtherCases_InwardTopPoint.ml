(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/InwardTopPoint.lean                 *)
(* (namespace N12Compact.Completion.OtherCases.InwardTopPoint).              *)
(* The inward square with an actual top anchor reaches the sharp common     *)
(* point.  short_projections: WFP_SP; canonical_frame: CLF_CANONICAL_FRAME. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let OCITP_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* linear arithmetic ignoring universally quantified and negated assumptions *)
let OCITP_LIN0_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) || (is_neg(concl th) && can (find_term ((=) `linside`)) (concl th))
    then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCITP_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_point (private) *)
let OCITP_POSITIVE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&0) (&13 / &50) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&2 / &5) (&1) /\
      ~linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
      ~linside c s u v a (&7 / &20) (--(&7 / &20))
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  MP_TAC(WFP_SP `--(&53 / &200)` `&7 / &8`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `c / &6 <= s` THENL
   [SUBGOAL_THEN `v + a <= --s * &13 / &50 + c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~linside c s u v a (&13 / &50) (&1)` THEN REWRITE_TAC[] THEN
      OCITP_LIN0_TAC;
      OCITP_LIN0_TAC];
    SUBGOAL_THEN `--s * &7 / &20 + c * --(&7 / &20) <= v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~linside c s u v a (&7 / &20) (--(&7 / &20))` THEN REWRITE_TAC[] THEN
      OCITP_LIN0_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c * --(&7 / &20) + s * &7 / &20 <= u` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~linside c s u v a (--(&7 / &20)) (&7 / &20)` THEN REWRITE_TAC[] THEN
      OCITP_LIN0_TAC;
      OCITP_LIN0_TAC]]);;

(* Lean: negative_point (private) *)
let OCITP_NEGATIVE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&0) (&13 / &50) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&2 / &5) (&1) /\
      ~linside c s u v a (&13 / &50) (&1)
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&53 / &200` `--(&7 / &8)`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN OCITP_LIN_TAC);;

(* Lean: point *)
let OCITP_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&0) (&13 / &50) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&2 / &5) (&1) /\
      ~linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
      ~linside c s u v a (&7 / &20) (--(&7 / &20))
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
    else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OCITP_POSITIVE_POINT; MATCH_MP_TAC OCITP_NEGATIVE_POINT] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: point_original *)
let OCITP_POINT_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&47 / &20) (&47 / &20) /\
      linside c s u v a (&2) (&113 / &50) /\
      linside c s u v a (&113 / &50) (&2) /\
      linside c s u v a (&12 / &5) (&3) /\
      ~linside c s u v a (&113 / &50) (&3) /\
      ~linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&47 / &20) (&33 / &20)
      ==> linside c s u v a (&101 / &40) (&17 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCITP_POINT) THEN
  REWRITE_TAC[OCITP_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
