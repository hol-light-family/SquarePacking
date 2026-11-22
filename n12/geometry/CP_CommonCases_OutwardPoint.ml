(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/OutwardPoint.lean                  *)
(* (N12Compact.CommonCases.OutwardPoint).  The positive canonical outward    *)
(* square owns the same strict point as InwardPoint.                         *)
(* pullY: LINSIDE_PULLY;  q.translated dx dy is                              *)
(* (c, s, u - (c dx + s dy), v - (--s dx + c dy), a).                        *)
(* C981CompletionOutwardAnchor.nonnegative_impossible:                       *)
(* C981OA_NONNEGATIVE_IMPOSSIBLE.                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_C981_OutwardAnchor.ml";;

let CCOP_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCOP_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths));;

(* linear arithmetic with one missing-point hypothesis `~linside ...` *)
let CCOP_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

(* Lean: positive_point *)
let CCOP_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&1) (&13 / &50) /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&543 / &500) (&0) /\
     ~linside c s u v a (&13 / &50) (&1) /\
     ~linside c s u v a (&4 / &5) (&1) /\
     ~linside c s u v a (&1) (&1) /\
     ~linside c s u v a (&543 / &500) (&1)
     ==> linside c s u v a (&23 / &50) (-- &1 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CCOP_UNFOLD_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  SUBGOAL_THEN `v < --s * (&13 / &50)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCOP_NFACT_TAC `~linside c s u v a (&13 / &50) (&1)` `c * (&13 / &50) + s * &1 <= u` THEN
    CCOP_NFACT_TAC `~linside c s u v a (&4 / &5) (&1)` `u + a <= c * (&4 / &5) + s * &1` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  CCOP_NFACT_TAC `~linside c s u v a (&13 / &50) (&0)` `c * (&13 / &50) <= u` THEN
  CCOP_NFACT_TAC `~linside c s u v a (&543 / &500) (&0)` `--s * (&543 / &500) <= v` THEN
  CCOP_NFACT_TAC `~linside c s u v a (&543 / &500) (&1)`
    `u + a <= c * (&543 / &500) + s` THEN
  SUBGOAL_THEN `&87 / &500 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &1`]
   [`c <= &1 - s * s / &2`; `&0 < s * (s - &43 / &250)`; `c + (&43 / &500) * s < &1`] THEN
  CCOP_NFACT_TAC `~linside c s u v a (&1) (&1)` `u + a <= c + s` THEN
  SUBGOAL_THEN `u < c * (&23 / &50) + s * (-- &1 / &100)` ASSUME_TAC THENL
   [ASM_CASES_TAC `u + a <= c * (&4 / &5) + s` THENL
     [MP_TAC(SPECL [`c:real`; `s:real`; `&17 / &50`; `&101 / &100`]
        CCOS_INCREASING_PROJECTION) THEN
      ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      RASM_ARITH_TAC;
      CCOP_NFACT_TAC `~linside c s u v a (&4 / &5) (&1)` `v + a <= --s * (&4 / &5) + c` THEN
      MP_TAC(SPECL [`c:real`; `s:real`] CCOS_SHALLOW_PROJECTION) THEN
      ASM_REWRITE_TAC[REAL_POW_2] THEN
      ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `v < --s * (&23 / &50) + c * (-- &1 / &100)` ASSUME_TAC THENL
   [ASM_CASES_TAC `c <= &2 * s` THENL
     [RASM_ARITH_TAC;
      SUBGOAL_THEN `s < &9 / &20` ASSUME_TAC THENL
       [NLIN_FACTS_TAC [] [`&0 <= (c - &2 * s) * (c + &2 * s)`] THEN NLIN_TAC [];
        ALL_TAC] THEN
      CCOP_NFACT_TAC `~linside c s u v a (&4 / &5) (&1)` `v + a <= --s * (&4 / &5) + c` THEN
      RASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: positive_point_original *)
let CCOP_POSITIVE_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&14 / &5) (&3) /\
     ~linside c s u v a (&3) (&3) /\
     ~linside c s u v a (&1543 / &500) (&3)
     ==> linside c s u v a (&123 / &50) (&199 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] CCOP_POSITIVE_POINT) THEN
  REWRITE_TAC[CCOP_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: point_original *)
let CCOP_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&3) (&113 / &50) /\ linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&3) (&3) /\
     ~linside c s u v a (&1543 / &500) (&3) /\
     (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside c s u v a z (&3))
     ==> linside c s u v a (&123 / &50) (&199 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) then
    ASSUME_TAC(REWRITE_RULE[](CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
      (SPEC `&113 / &50` th))) THEN
    ASSUME_TAC(REWRITE_RULE[](CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
      (SPEC `&14 / &5` th)))
    else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC CCOP_POSITIVE_POINT_ORIGINAL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC C981OA_NONNEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `--sr`; `ur - &4 * sr`; `&4 * cr - vr - a`; `a:real`] THEN
    REWRITE_TAC[LINSIDE_PULLY] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) then
       (X_GEN_TAC `z:real` THEN STRIP_TAC THEN
        FIRST_ASSUM(fun th -> if is_forall(concl th) then MP_TAC(SPEC `z:real` th)
                              else NO_TAC) THEN
        DISCH_THEN(fun th -> ACCEPT_TAC(MP (MP th (ASSUME `&113 / &50 <= z`))
                                            (ASSUME `z <= &14 / &5`)))) g
     else ASM_REAL_ARITH_TAC g)]);;
