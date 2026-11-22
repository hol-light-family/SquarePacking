(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OutwardBarFrame.lean                *)
(* (namespace N12Compact.Completion.OtherCases.OutwardBarFrame).  The       *)
(* canonical frame and full faces underlying OutwardBarPoint.  Faces /      *)
(* positive_faces: ocobp_faces / OCOBP_POSITIVE_FACES; q.translated 2 2 is  *)
(* (c, s, u - (c * &2 + s * &2), v - (--s * &2 + c * &2), a);              *)
(* C981CompletionOutwardAnchor.nonnegative_impossible:                      *)
(* C981OA_NONNEGATIVE_IMPOSSIBLE; pullY: LINSIDE_PULLY.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarPoint.ml";;

(* Lean: faces_original *)
let OCOBF_FACES_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&47 / &20) (&47 / &20) /\
      linside c s u v a (&3) (&113 / &50) /\
      ~linside c s u v a (&113 / &50) (&2) /\
      ~linside c s u v a (&1543 / &500) (&2) /\
      ~linside c s u v a (&3) (&3) /\
      ~linside c s u v a (&1543 / &500) (&3) /\
      (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside c s u v a z (&3))
      ==> ocobp_faces c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCOBP_POSITIVE_FACES) THEN
  REWRITE_TAC[OCOBP_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: frame_original *)
let OCOBF_FRAME_ORIGINAL = prove
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
      ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
            &0 < c' /\ &0 <= s' /\ s' <= c' /\ a' = a /\
            (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
            ocobp_faces c' s' (u' - (c' * &2 + s' * &2)) (v' - (--s' * &2 + c' * &2)) a'`,
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
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OCOBF_FACES_ORIGINAL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC C981OA_NONNEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `--s1`; `u1 - &4 * s1`; `&4 * c1 - v1 - a`; `a:real`] THEN
    REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `z:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[]]);;
