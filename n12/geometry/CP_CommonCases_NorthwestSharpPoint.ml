(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/NorthwestSharpPoint.lean           *)
(* (N12Compact.CommonCases.NorthwestSharpPoint).  The sharp NW point of      *)
(* OTHER-GEOMETRY Theorem 10.                                                *)
(* chart q (private) is (c, s, v - 2c + 2s, --u - a + 2c + 2s, a), with      *)
(* inside_chart: CCNWS_INSIDE_CHART.  The square                             *)
(* turnFrame^3 (pullSwap r) is (c, --s, v, u, a) (CCNWS_SWAPPED).            *)
(* LowerSegmentSupport.support: CCLSS_SUPPORT;                               *)
(* C981CompletionOutwardAnchor.nonnegative_impossible:                       *)
(* C981OA_NONNEGATIVE_IMPOSSIBLE.                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_CommonCases_LowerSegmentSupport.ml";;
needs "n12/geometry/CP_C981_OutwardAnchor.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let CCNWS_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths));;

(* linear arithmetic with one missing-point hypothesis `~linside ...` *)
let CCNWS_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

let CCNWS_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let CCNWS_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* CanonicalProjection.before / after at the rational endpoint (c0,s0),     *)
(* added as an assumption                                                   *)
let CCNWS_PROJ_TAC th c0 s0 a b =
  let th' = SPECL [`c:real`; `s:real`; c0; s0; a; b] th in
  SUBGOAL_THEN (rand(concl th')) ASSUME_TAC THENL
   [MATCH_MP_TAC th' THEN REWRITE_TAC[REAL_POW_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC];;

(* Lean: top_support (private) *)
let CCNWS_TOP_SUPPORT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     u < c * (&13 / &50) + s /\ c * (&13 / &50) + s < u + a /\
     v + a <= c - s * (&13 / &50) /\
     u + a <= c * (&4 / &5) + s /\
     v < c - s * (&4 / &5) /\ c - s * (&4 / &5) < v + a /\
     (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside c s u v a x (&1))
     ==> s * (u + a) + c * (v + a) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--(u + a)`; `--u:real`; `--(v + a)`; `--v:real`;
    `--(c * (&4 / &5) + s)`; `--(c - s * (&4 / &5))`;
    `--(c * (&13 / &50) + s)`; `--(c - s * (&13 / &50))`] CCLSS_SUPPORT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    X_GEN_TAC `w:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) then
      MP_TAC(MP (MP (SPEC `(&1 - w) * (&4 / &5) + w * (&13 / &50)` th)
        (REAL_ARITH `w <= &1 ==> &13 / &50 <= (&1 - w) * (&4 / &5) + w * (&13 / &50)`
         |> C MP (ASSUME `w <= &1`)))
        (REAL_ARITH `&0 <= w ==> (&1 - w) * (&4 / &5) + w * (&13 / &50) <= &4 / &5`
         |> C MP (ASSUME `&0 <= w`)))
      else NO_TAC) THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RASM_ARITH_TAC);;

let CCNWS_AVOID_HYP =
  `forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside c s u v a x (&1)`;;

(* Lean: positive_points *)
let CCNWS_POSITIVE_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&1) (&13 / &50) /\
     ~linside c s u v a (&13 / &50) (&0) /\ ~linside c s u v a (&1) (&0) /\
     ~linside c s u v a (&1) (&1) /\
     (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside c s u v a x (&1))
     ==> linside c s u v a (&121 / &300) (-- &1 / &6) /\
         linside c s u v a (&3 / &5) (-- &1 / &10)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if aconv (concl th) CCNWS_AVOID_HYP then
    ASSUME_TAC(REWRITE_RULE[](CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
      (SPEC `&13 / &50` th))) THEN
    ASSUME_TAC(REWRITE_RULE[](CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
      (SPEC `&4 / &5` th)))
    else NO_TAC) THEN
  CCNWS_UNFOLD_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  SUBGOAL_THEN `v < --s * (&13 / &50)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCNWS_NFACT_TAC `~linside c s u v a (&13 / &50) (&1)` `c * (&13 / &50) + s * &1 <= u` THEN
    CCNWS_NFACT_TAC `~linside c s u v a (&4 / &5) (&1)` `u + a <= c * (&4 / &5) + s * &1` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  CCNWS_NFACT_TAC `~linside c s u v a (&13 / &50) (&0)` `c * (&13 / &50) <= u` THEN
  CCNWS_NFACT_TAC `~linside c s u v a (&1) (&0)` `--s <= v` THEN
  CCNWS_NFACT_TAC `~linside c s u v a (&1) (&1)` `u + a <= c + s` THEN
  CCNWS_NFACT_TAC `~linside c s u v a (&13 / &50) (&1)` `v + a <= --s * (&13 / &50) + c` THEN
  SUBGOAL_THEN `v + a <= --s * (&4 / &5) + c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    CCNWS_NFACT_TAC `~linside c s u v a (&4 / &5) (&1)` `u + a <= c * (&4 / &5) + s` THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCNWS_TOP_SUPPORT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); DISCH_TAC] THEN
    CCNWS_LE_MUL_TAC `s:real` `u - c * (&13 / &50)` THEN
    CCNWS_LE_MUL_TAC `c:real` `v + s` THEN
    CCNWS_LT_MUL_TAC `a - &1` `c + s` THEN
    CCNWS_LE_MUL_TAC `c:real` `s:real` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&12 / &13) * s < (&5 / &13) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCNWS_PROJ_TAC CCCP_AFTER `&12 / &13` `&5 / &13` `&1` `&1 / &5` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1131 / &3869) * c < (&3700 / &3869) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCNWS_PROJ_TAC CCCP_BEFORE `&3700 / &3869` `&1131 / &3869` `&37 / &50` `&1` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  CCNWS_PROJ_TAC CCCP_BEFORE `&12 / &13` `&5 / &13` `&179 / &300` `&7 / &6` THEN
  CCNWS_PROJ_TAC CCCP_AFTER `&3700 / &3869` `&1131 / &3869` `&7 / &6` `-- &119 / &300` THEN
  CCNWS_PROJ_TAC CCCP_BEFORE `&12 / &13` `&5 / &13` `&2 / &5` `&11 / &10` THEN
  CCNWS_PROJ_TAC CCCP_AFTER `&3700 / &3869` `&1131 / &3869` `&11 / &10` `-- &1 / &5` THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: positive_point *)
let CCNWS_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&1) (&13 / &50) /\
     ~linside c s u v a (&13 / &50) (&0) /\ ~linside c s u v a (&1) (&0) /\
     ~linside c s u v a (&1) (&1) /\
     (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside c s u v a x (&1))
     ==> linside c s u v a (&121 / &300) (-- &1 / &6)`,
  MESON_TAC[CCNWS_POSITIVE_POINTS]);;

(* Lean: chart (private definition) / inside_chart (private) *)
let CCNWS_INSIDE_CHART = prove
 (`forall c s u v a x y.
     linside c s (v - &2 * c + &2 * s) (--u - a + &2 * c + &2 * s) a x y <=>
     linside c s u v a (&2 - y) (&2 + x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCNWS_SWAPPED = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: points_original *)
let CCNWS_POINTS_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&8 / &5) (&3) /\ linside c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&2) (&113 / &50) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&1) (&3) /\ ~linside c s u v a (&2) (&1543 / &500) /\
     (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside c s u v a (&1) z)
     ==> linside c s u v a (&13 / &6) (&721 / &300) /\
         linside c s u v a (&21 / &10) (&13 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  SUBGOAL_THEN `&0 < sr` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MATCH_MP_TAC C981OA_NONNEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `--sr`; `vr:real`; `ur:real`; `a:real`] THEN
    REWRITE_TAC[CCNWS_SWAPPED] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) then ASM_MESON_TAC[] g else ASM_REAL_ARITH_TAC g);
    ALL_TAC] THEN
  MP_TAC(SPECL [`cr:real`; `sr:real`; `vr - &2 * cr + &2 * sr`;
                `--ur - a + &2 * cr + &2 * sr`; `a:real`] CCNWS_POSITIVE_POINTS) THEN
  REWRITE_TAC[CCNWS_INSIDE_CHART] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) then
      (X_GEN_TAC `x:real` THEN DISCH_TAC THEN DISCH_TAC THEN
       FIRST_ASSUM(fun th -> if is_forall(concl th) then MP_TAC(SPEC `&2 + x` th)
                             else NO_TAC) THEN
       ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]) g
     else ASM_REAL_ARITH_TAC g);
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* Lean: point_original *)
let CCNWS_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&8 / &5) (&3) /\ linside c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&2) (&113 / &50) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&1) (&3) /\ ~linside c s u v a (&2) (&1543 / &500) /\
     (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside c s u v a (&1) z)
     ==> linside c s u v a (&13 / &6) (&721 / &300)`,
  MESON_TAC[CCNWS_POINTS_ORIGINAL]);;

(* Lean: upper_point_original *)
let CCNWS_UPPER_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&8 / &5) (&3) /\ linside c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&2) (&113 / &50) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&1) (&3) /\ ~linside c s u v a (&2) (&1543 / &500) /\
     (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside c s u v a (&1) z)
     ==> linside c s u v a (&21 / &10) (&13 / &5)`,
  MESON_TAC[CCNWS_POINTS_ORIGINAL]);;
