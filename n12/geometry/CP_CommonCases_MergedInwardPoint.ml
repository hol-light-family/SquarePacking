(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/MergedInwardPoint.lean             *)
(* (N12Compact.CommonCases.MergedInwardPoint).  MERGED-RIGHT-PATTERN-4      *)
(* Theorem B: the sharp foreign NW point forces the merged owner to contain *)
(* the southwest duplicate point.  S12.short_projections: WFP_SP;           *)
(* q.translated dx dy is (c, s, u - (c dx + s dy), v - (--s dx + c dy), a).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let CCMIP_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCMIP_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths));;

(* linear arithmetic with one missing-point hypothesis `~linside ...` *)
let CCMIP_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

(* Lean: negative_impossible (private) *)
let CCMIP_NEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&7 / &20) (-- &7 / &20) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&0) (-- &13 / &50) /\
     ~linside c s u v a (&1 / &6) (&121 / &300)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&199 / &300` `-- &1 / &6`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  CCMIP_UNFOLD_TAC THEN
  CCMIP_NFACT_TAC `~linside c (--t) u v a (&0) (-- &13 / &50)`
    `c * (-- &13 / &50) <= v` THEN
  CCMIP_NFACT_TAC `~linside c (--t) u v a (&1 / &6) (&121 / &300)`
    `v + a <= t * (&1 / &6) + c * (&121 / &300)` THEN
  RASM_ARITH_TAC);;

(* Lean: positive (private) *)
let CCMIP_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (-- &7 / &20) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&0) (-- &13 / &50) /\
     ~linside c s u v a (&1) (-- &13 / &50) /\
     ~linside c s u v a (&543 / &500) (&0) /\
     ~linside c s u v a (&1 / &6) (&121 / &300)
     ==> linside c s u v a (-- &1 / &20) (-- &1 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CCMIP_UNFOLD_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  CCMIP_NFACT_TAC `~linside c s u v a (&0) (-- &13 / &50)`
    `s * (-- &13 / &50) <= u` THEN
  CCMIP_NFACT_TAC `~linside c s u v a (&1) (-- &13 / &50)`
    `--s + c * (-- &13 / &50) <= v` THEN
  CCMIP_NFACT_TAC `~linside c s u v a (&1 / &6) (&121 / &300)`
    `v + a <= --s * (&1 / &6) + c * (&121 / &300)` THEN
  SUBGOAL_THEN `(&175 / &337) * c < (&288 / &337) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `&288 / &337`; `&175 / &337`;
                  `&199 / &300`; `&5 / &6`] CCCP_BEFORE) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&121 / &300`; `&1379 / &1500`]
    CCOS_INCREASING_PROJECTION) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  CCMIP_NFACT_TAC `~linside c s u v a (&543 / &500) (&0)`
    `u + a <= c * (&543 / &500) + s * &0` THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&288 / &337`; `&175 / &337`;
                `&142 / &125`; `&1 / &20`] CCCP_AFTER) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: point *)
let CCMIP_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&7 / &20) (-- &7 / &20) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&0) (-- &13 / &50) /\
     ~linside c s u v a (&1) (-- &13 / &50) /\
     ~linside c s u v a (&543 / &500) (&0) /\
     ~linside c s u v a (&1 / &6) (&121 / &300)
     ==> linside c s u v a (-- &1 / &20) (-- &1 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC CCMIP_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC CCMIP_NEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`; `--sr`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: point_original *)
let CCMIP_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&2) (&113 / &50) /\
     ~linside c s u v a (&2) (&87 / &50) /\
     ~linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&13 / &6) (&721 / &300)
     ==> linside c s u v a (&39 / &20) (&39 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] CCMIP_POINT) THEN
  REWRITE_TAC[CCMIP_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;
