(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/MergedNearPoint.lean               *)
(* (N12Compact.CommonCases.MergedNearPoint).  OTHER-GEOMETRY Theorem 11,     *)
(* proved directly from forced faces.                                        *)
(* pullY (r.translated 0 (-4)), the reflection y -> -y, is the square        *)
(* (c, --s, u, --v - a, a) (CCMNP_REFLECT);  q.translated dx dy is           *)
(* (c, s, u - (c dx + s dy), v - (--s dx + c dy), a).                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let CCMNP_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCMNP_REFLECT = prove
 (`forall c s u v a x y. linside c (--s) u (--v - a) a x y <=> linside c s u v a x (--y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCMNP_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths));;

(* linear arithmetic with one missing-point hypothesis `~linside ...` *)
let CCMNP_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

(* Lean: positive (private) *)
let CCMNP_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (-- &7 / &20) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (&0) (-- &13 / &50) /\
     ~linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&1) (-- &13 / &50) /\
     ~linside c s u v a (&1) (&13 / &50) /\
     ~linside c s u v a (&543 / &500) (&0)
     ==> linside c s u v a (-- &1 / &20) (-- &1 / &20) /\
         linside c s u v a (-- &1 / &20) (&1 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CCMNP_UNFOLD_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  CCMNP_NFACT_TAC `~linside c s u v a (&0) (-- &13 / &50)`
    `s * (-- &13 / &50) <= u` THEN
  CCMNP_NFACT_TAC `~linside c s u v a (&1) (-- &13 / &50)`
    `--s + c * (-- &13 / &50) <= v` THEN
  SUBGOAL_THEN `v + a <= c * (&13 / &50)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    CCMNP_NFACT_TAC `~linside c s u v a (&0) (&13 / &50)` `s * (&13 / &50) <= u` THEN
    CCMNP_NFACT_TAC `~linside c s u v a (&1) (&13 / &50)` `--s + c * (&13 / &50) <= v` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  CCMNP_NFACT_TAC `~linside c s u v a (&1) (&13 / &50)` `u + a <= c + s * (&13 / &50)` THEN
  SUBGOAL_THEN `(&228 / &397) * c < (&325 / &397) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `&325 / &397`; `&228 / &397`;
                  `&13 / &25`; `&1`] CCCP_BEFORE) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &50`; `&543 / &500`]
    CCOS_INCREASING_PROJECTION) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  CCMNP_NFACT_TAC `~linside c s u v a (&543 / &500) (&0)`
    `u + a <= c * (&543 / &500) + s * &0` THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&325 / &397`; `&228 / &397`;
                `&142 / &125`; `&1 / &20`] CCCP_AFTER) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&31 / &100`; `&21 / &20`]
    CCOS_INCREASING_PROJECTION) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: points *)
let CCMNP_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&7 / &20) (-- &7 / &20) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (&0) (-- &13 / &50) /\
     ~linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&1) (-- &13 / &50) /\
     ~linside c s u v a (&1) (&13 / &50) /\
     ~linside c s u v a (&543 / &500) (&0)
     ==> linside c s u v a (-- &1 / &20) (-- &1 / &20) /\
         linside c s u v a (-- &1 / &20) (&1 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC CCMNP_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`cr:real`; `--sr`; `ur:real`; `--vr - a`; `a:real`] CCMNP_POSITIVE) THEN
    REWRITE_TAC[CCMNP_REFLECT] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]]);;

(* Lean: points_original *)
let CCMNP_POINTS_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&2) (&87 / &50) /\
     ~linside c s u v a (&2) (&113 / &50) /\
     ~linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&1543 / &500) (&2)
     ==> linside c s u v a (&39 / &20) (&39 / &20) /\
         linside c s u v a (&39 / &20) (&41 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] CCMNP_POINTS) THEN
  REWRITE_TAC[CCMNP_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;
