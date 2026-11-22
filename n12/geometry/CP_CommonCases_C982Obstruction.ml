(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C982Obstruction.lean               *)
(* (N12Compact.CommonCases.C982Obstruction).  C982's one-segment,           *)
(* three-point obstruction.  The private predicate Avoid q is written out    *)
(* inline in each statement.  S12.short_projections: WFP_SP;                 *)
(* SegmentSupport: CCSS_*; CanonicalScalars: CCCS_*.                         *)
(* q.translated dx dy is (c, s, u - (c dx + s dy), v - (--s dx + c dy), a).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_SegmentSupport.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let CCC982_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCC982_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let CCC982_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* linear arithmetic with one missing-point hypothesis `~linside ...` *)
let CCC982_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

let CCC982_NCONTRA_TAC n =
  MP_TAC(ASSUME n) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* the origin is owned: the four anchor inequalities *)
let CCC982_ORIGIN_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `linside c s u v a (&0) (&0)`) (concl th)
    then STRIP_ASSUME_TAC(REWRITE_RULE[linside] th) else NO_TAC);;

(* discharge the segment-avoidance premise of a SegmentSupport lemma from   *)
(* the (inline) Avoid hypothesis                                            *)
let CCC982_SEGMENT_TAC =
  X_GEN_TAC `w:real` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) then
    MP_TAC(MP (MP (SPEC `w:real` th) (ASSUME `&0 <= w`)) (ASSUME `w <= &1`))
    else NO_TAC) THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let CCC982_PREMISES_TAC =
  REPEAT CONJ_TAC THEN
  (fun g -> if is_forall(snd g) then CCC982_SEGMENT_TAC g else RASM_ARITH_TAC g);;

(* Lean: positive_support (private) *)
let CCC982_POSITIVE_SUPPORT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&0) (&0) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (-- &7 / &20) + w * (-- &1 / &20))
                           ((&1 - w) * (-- &92 / &125) + w * (&19 / &100)))
     ==> (--(&1 / &20) * c + (&19 / &100) * s <= u /\
          --(&7 / &20) * c - (&92 / &125) * s <= u) \/
         (&463 / &500 * c - &3 / &10 * s) * u -
         (&3 / &10 * c + &463 / &500 * s) * (v + a) >= --(&1033 / &10000)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CCC982_ORIGIN_TAC THEN
  MP_TAC(WFP_SP `&3 / &10` `&463 / &500`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real`; `u + a:real`; `v:real`; `v + a:real`;
    `--(&7 / &20) * c - (&92 / &125) * s`; `(&7 / &20) * s - (&92 / &125) * c`;
    `--(&1 / &20) * c + (&19 / &100) * s`; `(&1 / &20) * s + (&19 / &100) * c`]
    CCSS_INCREASING) THEN
  ANTS_TAC THENL [CCC982_PREMISES_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_support (private) *)
let CCC982_NEGATIVE_SUPPORT = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&0) (&0) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (-- &7 / &20) + w * (-- &1 / &20))
                           ((&1 - w) * (-- &92 / &125) + w * (&19 / &100)))
     ==> (--(&1 / &20) * c - (&19 / &100) * t <= u /\
          --(&7 / &20) * c + (&92 / &125) * t <= u) \/
         ((&0 <= &463 / &500 * t - &3 / &10 * c /\
           (&463 / &500 * c + &3 / &10 * t) * u +
           (&463 / &500 * t - &3 / &10 * c) * v >= --(&1033 / &10000)) \/
          (&463 / &500 * t - &3 / &10 * c < &0 /\
           (&463 / &500 * c + &3 / &10 * t) * u +
           (&463 / &500 * t - &3 / &10 * c) * (v + a) >= --(&1033 / &10000)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CCC982_ORIGIN_TAC THEN
  MP_TAC(WFP_SP `&3 / &10` `&463 / &500`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  let U0 = `--(&7 / &20) * c + (&92 / &125) * t`
  and V0 = `--(&7 / &20) * t - (&92 / &125) * c`
  and U1 = `--(&1 / &20) * c - (&19 / &100) * t`
  and V1 = `--(&1 / &20) * t + (&19 / &100) * c` in
  let args = [`u:real`; `u + a:real`; `v:real`; `v + a:real`; U0; V0; U1; V1] in
  ASM_CASES_TAC (mk_eq(U0,U1)) THENL
   [MP_TAC(SPECL args CCSS_VERTICAL) THEN
    ANTS_TAC THENL [CCC982_PREMISES_TAC; ALL_TAC] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC (mk_comb(mk_comb(`(<):real->real->bool`,U1),U0)) THENL
   [MP_TAC(SPECL args CCSS_DECREASING) THEN
    ANTS_TAC THENL [CCC982_PREMISES_TAC; ALL_TAC] THEN RASM_ARITH_TAC;
    MP_TAC(SPECL args CCSS_INCREASING) THEN
    ANTS_TAC THENL [CCC982_PREMISES_TAC; ALL_TAC] THEN RASM_ARITH_TAC]);;

(* Lean: positive_impossible (private) *)
let CCC982_POSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&0) (&0) /\
     ~linside c s u v a (&92 / &125) (-- &13 / &20) /\
     ~linside c s u v a (&92 / &125) (&7 / &20) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (-- &7 / &20) + w * (-- &1 / &20))
                           ((&1 - w) * (-- &92 / &125) + w * (&19 / &100)))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_POSITIVE_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  CCC982_ORIGIN_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCC982_POSITIVE_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC)] THENL
   [CCC982_NFACT_TAC `~linside c s u v a (&92 / &125) (-- &13 / &20)`
      `--s * (&92 / &125) + c * (-- &13 / &20) <= v` THEN
    CCC982_NCONTRA_TAC `~linside c s u v a (&92 / &125) (&7 / &20)`;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN
  CCC982_LT_MUL_TAC `&3 / &10 * c + &463 / &500 * s` `v + a:real` THEN
  CCC982_LT_MUL_TAC `&463 / &500 * c - &3 / &10 * s` `--u:real` THEN
  SUBGOAL_THEN `c * (&92 / &125) + s * (-- &13 / &20) < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCC982_LE_MUL_TAC `(&463 / &500 * c - &3 / &10 * s) - &2191 / &5000`
                      `--u - &33 / &125` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  CCC982_NFACT_TAC `~linside c s u v a (&92 / &125) (-- &13 / &20)`
    `--s * (&92 / &125) + c * (-- &13 / &20) <= v` THEN
  SUBGOAL_THEN `v < --s * (&92 / &125) + c * (&7 / &20)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCC982_LE_MUL_TAC `(&3 / &10 * c + &463 / &500 * s) - &21 / &100`
                      `(v + a) - &307 / &500` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  CCC982_NFACT_TAC `~linside c s u v a (&92 / &125) (&7 / &20)`
    `u + a <= c * (&92 / &125) + s * (&7 / &20)` THEN
  CCC982_LE_MUL_TAC `&463 / &500 * c - &3 / &10 * s`
                    `(c * (&92 / &125) + s * (&7 / &20)) - (u + a)` THEN
  CCC982_LE_MUL_TAC `&3 / &10 * c + &463 / &500 * s`
                    `v - (--s * (&92 / &125) + c * (-- &13 / &20))` THEN
  CCC982_LT_MUL_TAC `a - &1`
    `(&463 / &500 * c - &3 / &10 * s) + (&3 / &10 * c + &463 / &500 * s)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  RASM_ARITH_TAC);;

(* Lean: negative_impossible (private) *)
let CCC982_NEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&0) (&0) /\
     ~linside c s u v a (&13 / &20) (-- &13 / &20) /\
     ~linside c s u v a (&92 / &125) (-- &13 / &20) /\
     ~linside c s u v a (&92 / &125) (&7 / &20) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (-- &7 / &20) + w * (-- &1 / &20))
                           ((&1 - w) * (-- &92 / &125) + w * (&19 / &100)))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`]
    CCC982_NEGATIVE_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  CCC982_ORIGIN_TAC THEN
  let H = `~linside c (--t) u v a (&92 / &125) (-- &13 / &20)`
  and R = `~linside c (--t) u v a (&92 / &125) (&7 / &20)`
  and P = `~linside c (--t) u v a (&13 / &20) (-- &13 / &20)` in
  let uh = `(&92 / &125) * c + (&13 / &20) * t`
  and vh = `(&92 / &125) * t - (&13 / &20) * c`
  and ur = `(&92 / &125) * c - (&7 / &20) * t`
  and vr = `(&92 / &125) * t + (&7 / &20) * c`
  and up = `(&13 / &20) * (c + t)`
  and vp = `(&13 / &20) * (t - c)` in
  let rel op x y = mk_comb(mk_comb(op,x),y) in
  let lt = rel `(<):real->real->bool` and le = rel `(<=):real->real->bool` in
  let al = `&463 / &500 * c + &3 / &10 * t` in
  FIRST_X_ASSUM(DISJ_CASES_THEN2 STRIP_ASSUME_TAC ASSUME_TAC o check (is_disj o concl)) THENL
   [(* face case *)
    CCC982_NFACT_TAC R (le `v + a:real` vr) THEN
    CCC982_NFACT_TAC H (le `u + a:real` uh) THEN
    CCC982_NFACT_TAC P (le vp `v:real`) THEN
    ASM_CASES_TAC `c <= &5 * t` THENL
     [MP_TAC(SPECL [`c:real`; `t:real`] CCCS_C_SMALL_SINE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN RASM_ARITH_TAC;
      RASM_ARITH_TAC];
    ALL_TAC] THEN
  (* support cases: negU *)
  SUBGOAL_THEN (le (mk_comb(mk_comb(`( * ):real->real->real`,al),`--u:real`)) `&1033 / &10000`)
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THENL
     [CCC982_LE_MUL_TAC `&463 / &500 * t - &3 / &10 * c` `--v:real`;
      CCC982_LT_MUL_TAC `--(&463 / &500 * t - &3 / &10 * c)` `v + a:real`] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (lt ur `u + a:real`) ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCC982_LE_MUL_TAC (mk_comb(mk_comb(`(-):real->real->real`,al),`&3241 / &5000`))
                      `--u - &33 / &125` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  CCC982_NFACT_TAC R (le `v + a:real` vr) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THENL
   [(* gamma >= 0 *)
    MP_TAC(SPECL [`c:real`; `t:real`] CCCS_C_SMALL_SINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    CCC982_NFACT_TAC P (le `u + a:real` up) THEN
    CCC982_LE_MUL_TAC al (mk_comb(mk_comb(`(-):real->real->real`,up),`u + a:real`)) THEN
    CCC982_LE_MUL_TAC `&463 / &500 * t - &3 / &10 * c`
                      (mk_comb(mk_comb(`(-):real->real->real`,vr),`v + a:real`)) THEN
    CCC982_LT_MUL_TAC `a - &1` `(&463 / &500 * c + &3 / &10 * t) +
                                 (&463 / &500 * t - &3 / &10 * c)` THEN
    MP_TAC(SPECL [`c:real`; `t:real`] CCCS_NEGATIVE_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    RASM_ARITH_TAC;
    (* gamma < 0 *)
    CCC982_NFACT_TAC H (le `u + a:real` uh) THEN
    ASM_CASES_TAC `&5 * t <= c` THENL
     [CCC982_LE_MUL_TAC `c - &5 * t` `c + &5 * t` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
      SUBGOAL_THEN `&49 / &50 < c` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
      CCC982_LE_MUL_TAC (mk_comb(mk_comb(`(-):real->real->real`,al),`&9 / &10`))
                        `--u - &67 / &500` THEN
      RASM_ARITH_TAC;
      MP_TAC(SPECL [`c:real`; `t:real`] CCCS_C_SMALL_SINE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
      CCC982_NFACT_TAC P (le `u + a:real` up) THEN
      CCC982_LE_MUL_TAC `c - &3 * t` `c + &3 * t` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
      SUBGOAL_THEN `&9 / &10 < c` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
      CCC982_LE_MUL_TAC (mk_comb(mk_comb(`(-):real->real->real`,al),`&4167 / &5000`))
                        `--u - &2 / &15` THEN
      RASM_ARITH_TAC]]);;

(* Lean: impossible *)
let CCC982_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&0) (&0) /\
     ~linside c s u v a (&13 / &20) (-- &13 / &20) /\
     ~linside c s u v a (&92 / &125) (-- &13 / &20) /\
     ~linside c s u v a (&92 / &125) (&7 / &20) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (-- &7 / &20) + w * (-- &1 / &20))
                           ((&1 - w) * (-- &92 / &125) + w * (&19 / &100)))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC CCC982_POSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CCC982_NEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`; `--sr`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: impossible_original *)
let CCC982_IMPOSSIBLE_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&3) (&1) /\
     ~linside c s u v a (&1543 / &500) (&1) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * &2 + w * (&23 / &10))
                           ((&1 - w) * (&457 / &500) + w * (&46 / &25)))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`;
    `u - (c * (&47 / &20) + s * (&33 / &20))`; `v - (--s * (&47 / &20) + c * (&33 / &20))`;
    `a:real`] CCC982_IMPOSSIBLE) THEN
  REWRITE_TAC[CCC982_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  CCC982_SEGMENT_TAC);;
