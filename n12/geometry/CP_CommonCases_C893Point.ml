(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C893Point.lean                     *)
(* (N12Compact.CommonCases.C893Point).  The owned corner marker of C893 and  *)
(* its G outward anchor force one of two points.                             *)
(* q.translated dx dy is (c, s, u - (c dx + s dy), v - (--s dx + c dy), a).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let CCC893_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCC893_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths));;

let CCC893_FACT_TAC t =
  SUBGOAL_THEN t ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC];;

(* linear arithmetic with one missing-point hypothesis `~linside ...` *)
let CCC893_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

(* Lean: positive (private) *)
let CCC893_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&1) (&2 / &5) /\
     linside c s u v a (&543 / &500) (&1) /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&543 / &500) (&0) /\
     ~linside c s u v a (&22 / &25) (&1)
     ==> linside c s u v a (&1 / &2) (&0) \/
         linside c s u v a (&27 / &50) (-- &1 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CCC893_UNFOLD_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  CCC893_NFACT_TAC `~linside c s u v a (&22 / &25) (&1)`
    `v + a <= --s * (&22 / &25) + c * &1` THEN
  CCC893_NFACT_TAC `~linside c s u v a (&13 / &50) (&0)` `c * (&13 / &50) <= u` THEN
  CCC893_NFACT_TAC `~linside c s u v a (&543 / &500) (&0)` `--s * (&543 / &500) <= v` THEN
  CCC893_FACT_TAC `&1 < c + (&103 / &500) * s` THEN
  CCC893_FACT_TAC `&0 < s` THEN
  SUBGOAL_THEN `&2 * s < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 < &239391 / &250000 * s - &103 / &250 * c`;
      `&0 < s * (&239391 / &250000 * s - &103 / &250 * c)`;
      `c + (&103 / &500) * s < &1`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  REWRITE_TAC[linside] THEN
  ASM_CASES_TAC `&20 * s < c` THENL
   [DISJ1_TAC THEN RASM_ARITH_TAC;
    NLIN_FACTS_TAC [] [`&0 <= (&20 * s - c) * (&20 * s + c)`; `&1 / &21 < s`] THEN
    DISJ2_TAC THEN RASM_ARITH_TAC]);;

(* Lean: negative_impossible (private) *)
let CCC893_NEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&543 / &500) (&1) /\
     ~linside c s u v a (&543 / &500) (&0) /\
     ~linside c s u v a (&22 / &25) (&1)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  CCC893_UNFOLD_TAC THEN
  CCC893_NFACT_TAC `~linside c (--t) u v a (&22 / &25) (&1)`
    `c * (&22 / &25) + --t * &1 <= u` THEN
  CCC893_FACT_TAC `&53 * c < &65 * t` THEN
  CCC893_NFACT_TAC `~linside c (--t) u v a (&543 / &500) (&0)`
    `u + a <= c * (&543 / &500) + --t * &0` THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `&103 / &500`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: points *)
let CCC893_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&1) (&2 / &5) /\
     linside c s u v a (&543 / &500) (&1) /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&543 / &500) (&0) /\
     ~linside c s u v a (&22 / &25) (&1)
     ==> linside c s u v a (&1 / &2) (&0) \/
         linside c s u v a (&27 / &50) (-- &1 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC CCC893_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC CCC893_NEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`; `--sr`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: points_original *)
let CCC893_POINTS_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&3) (&12 / &5) /\
     linside c s u v a (&1543 / &500) (&3) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&72 / &25) (&3)
     ==> linside c s u v a (&5 / &2) (&2) \/
         linside c s u v a (&127 / &50) (&199 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] CCC893_POINTS) THEN
  REWRITE_TAC[CCC893_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;
