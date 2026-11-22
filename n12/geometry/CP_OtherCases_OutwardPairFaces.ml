(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OutwardPairFaces.lean               *)
(* (namespace N12Compact.Completion.OtherCases.OutwardPairFaces).  The      *)
(* northeast frame forced by its omitted sharp point.  short_projections:   *)
(* WFP_SP; increasing_projection: CCOS_INCREASING_PROJECTION;               *)
(* canonical_frame: CLF_CANONICAL_FRAME.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/CP_OtherCases_OutwardPairScalars.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;

let OCOPF_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let OCOPF_STEP t keep =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCOPF_KEEP_TAC keep; ALL_TAC];;

(* Lean: negative_point (private) *)
let OCOPF_NEGATIVE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&1) (&1)
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  let mY = `~linside c s u v a (&21 / &40) (&1 / &8)`
  and mP0 = `~linside c s u v a (&0) (&1)`
  and mP1 = `~linside c s u v a (&1) (&1)` in
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  MP_TAC(SPECL [`c:real`; `--s`; `&21 / &40`; `&7 / &8`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(WFP_SP `&19 / &40` `&7 / &8`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  OCOPF_STEP `s <= u` [mP0] THEN
  OCOPF_STEP `--s * &21 / &40 + c * &1 / &8 <= v` [mY] THEN
  OCOPF_STEP `u + a <= c + s` [mP1] THEN
  OCOPF_KEEP_TAC []);;

(* Lean: positive_faces *)
let OCOPF_POSITIVE_FACES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&0) (&13 / &50) /\
      linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
      ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&1) (&1) /\
      ~linside c s u v a (&21 / &40) (&1 / &8)
      ==> &7 / &20 * (s - c) <= u /\ v + a <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  OCOPF_STEP `c * --(&7 / &20) + s * &7 / &20 <= u`
    [`~linside c s u v a (--(&7 / &20)) (&7 / &20)`] THEN
  OCOPF_STEP `--s * &21 / &40 + c * &1 / &8 <= v`
    [`~linside c s u v a (&21 / &40) (&1 / &8)`] THEN
  OCOPF_STEP `u + a <= c + s` [`~linside c s u v a (&1) (&1)`] THEN
  OCOPF_STEP `v + a <= c` [`~linside c s u v a (&0) (&1)`] THEN
  OCOPF_KEEP_TAC []);;

(* Lean: frame *)
let OCOPF_FRAME = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&0) (&13 / &50) /\
      linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
      ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&1) (&1) /\
      ~linside c s u v a (&21 / &40) (&1 / &8)
      ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
            &0 < c' /\ &0 <= s' /\ s' <= c' /\ a' = a /\
            (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
            &7 / &20 * (s' - c') <= u' /\ v' + a' <= c'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th) &&
       length(fst(strip_forall(concl th))) = 2 && is_eq(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OCOPF_POSITIVE_FACES THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    UNDISCH_TAC `~linside c1 s1 u1 v1 a (&21 / &40) (&1 / &8)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC OCOPF_NEGATIVE_POINT THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
