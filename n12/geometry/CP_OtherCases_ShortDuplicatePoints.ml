(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/ShortDuplicatePoints.lean           *)
(* (namespace N12Compact.Completion.OtherCases.ShortDuplicatePoints).       *)
(* Inward Theorem 2 of C974-C976-DUPLICATE-POINT and an outward corollary.  *)
(* short_projections: WFP_SP; CanonicalScalars.bounds: CCCS_BOUNDS;         *)
(* canonical_frame: CLF_CANONICAL_FRAME; OutwardBarPoint.point_original:    *)
(* OCOBP_POINT_ORIGINAL.  The Lean triangle certificate is replaced by the  *)
(* explicit convex weights 50/293, 3/293, 240/293.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let OCSDP_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let OCSDP_STEP t keep =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCSDP_KEEP_TAC keep; ALL_TAC];;

(* Lean: inward_positive *)
let OCSDP_INWARD_POSITIVE = prove
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
      ==> linside c s u v a (&1 / &2) (&1 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  ASM_CASES_TAC `c <= &6 * s` THENL
   [OCSDP_STEP `v + a <= --(&13 / &50) * s + c` [`~linside c s u v a (&13 / &50) (&1)`] THEN
    MP_TAC(WFP_SP `--(&6 / &25)` `&24 / &25`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    OCSDP_KEEP_TAC [];
    OCSDP_STEP `--(&7 / &20) * s - &7 / &20 * c <= v`
      [`~linside c s u v a (&7 / &20) (--(&7 / &20))`] THEN
    OCSDP_STEP `--(&7 / &20) * c + &7 / &20 * s <= u`
      [`~linside c s u v a (--(&7 / &20)) (&7 / &20)`] THEN
    OCSDP_KEEP_TAC []]);;

(* Lean: inward_negative *)
let OCSDP_INWARD_NEGATIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&0) (&13 / &50) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&2 / &5) (&1) /\
      ~linside c s u v a (&13 / &50) (&1)
      ==> linside c s u v a (&1 / &2) (&1 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OCSDP_STEP `&13 / &50 * c + s <= u` [`~linside c s u v a (&13 / &50) (&1)`] THEN
  MP_TAC(WFP_SP `&6 / &25` `--(&24 / &25)`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  OCSDP_KEEP_TAC []);;

(* Lean: inward *)
let OCSDP_INWARD = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&0) (&13 / &50) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&2 / &5) (&1) /\
      ~linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
      ~linside c s u v a (&7 / &20) (--(&7 / &20))
      ==> linside c s u v a (&1 / &2) (&1 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th) &&
       length(fst(strip_forall(concl th))) = 2 && is_eq(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OCSDP_INWARD_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OCSDP_INWARD_NEGATIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCSDP_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inward_original *)
let OCSDP_INWARD_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&47 / &20) (&47 / &20) /\
      linside c s u v a (&2) (&113 / &50) /\
      linside c s u v a (&113 / &50) (&2) /\
      linside c s u v a (&12 / &5) (&3) /\
      ~linside c s u v a (&113 / &50) (&3) /\
      ~linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&47 / &20) (&33 / &20)
      ==> linside c s u v a (&5 / &2) (&51 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCSDP_INWARD) THEN
  REWRITE_TAC[OCSDP_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: outward_of_bar *)
let OCSDP_OUTWARD_OF_BAR = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&47 / &20) (&47 / &20) /\
      linside c s u v a (&3) (&113 / &50) /\
      linside c s u v a (&3) (&12 / &5) /\
      ~linside c s u v a (&113 / &50) (&2) /\
      ~linside c s u v a (&1543 / &500) (&2) /\
      ~linside c s u v a (&3) (&3) /\
      ~linside c s u v a (&1543 / &500) (&3) /\
      (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside c s u v a z (&3))
      ==> linside c s u v a (&5 / &2) (&49 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCOBP_POINT_ORIGINAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OCSDP_KEEP_TAC []);;
