(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C702NorthPoint.lean                *)
(* (N12Compact.CommonCases.C702NorthPoint).  C702-N-STRICT-POINT, with both  *)
(* whole foreign segments retained.  The private predicates TopAvoid and     *)
(* LeftAvoid are written out inline.  LowerSegmentSupport.support:           *)
(* CCLSS_SUPPORT; C702NorthScalars: CCC702N_*; CanonicalProjection: CCCP_*.  *)
(* q.translated dx dy is (c, s, u - (c dx + s dy), v - (--s dx + c dy), a).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_C702NorthScalars.ml";;
needs "n12/geometry/CP_CommonCases_LowerSegmentSupport.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let CCC702P_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let ccc702p_top =
  `forall x. &1 / &5 <= x ==> x <= &37 / &50 ==> ~linside c s u v a x (&1)`;;
let ccc702p_left =
  `forall w. &0 <= w ==> w <= &1 ==>
       ~linside c s u v a ((&1 - w) * (-- &6 / &25))
                          ((&1 - w) * (-- &13 / &100) + w * (-- &13 / &50))`;;

(* the avoidance hypothesis hyp (an assumption) at the numeral x0 *)
let CCC702P_INST_TAC hyp x0 =
  ASSUME_TAC(REWRITE_RULE[] (CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (SPEC x0 (ASSUME hyp))));;

let CCC702P_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths));;

(* linear arithmetic with one missing-point hypothesis `~linside ...` *)
let CCC702P_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

let CCC702P_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let CCC702P_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let CCC702P_PROJ_TAC th c0 s0 a b =
  let th' = SPECL [`c:real`; `s:real`; c0; s0; a; b] th in
  SUBGOAL_THEN (rand(concl th')) ASSUME_TAC THENL
   [MATCH_MP_TAC th' THEN REWRITE_TAC[REAL_POW_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC];;

(* instance th' (an implication) of a scalar lemma, conclusion as assumption *)
let CCC702P_USE_TAC th' =
  SUBGOAL_THEN (rand(concl th')) ASSUME_TAC THENL
   [MATCH_MP_TAC th' THEN REWRITE_TAC[REAL_POW_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC];;

(* Lean: top_support (private) *)
let CCC702P_TOP_SUPPORT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     u < c * (&1 / &5) + s /\ c * (&1 / &5) + s < u + a /\
     v + a <= c - s * (&1 / &5) /\
     u + a <= c * (&37 / &50) + s /\
     v < c - s * (&37 / &50) /\ c - s * (&37 / &50) < v + a /\
     (forall x. &1 / &5 <= x ==> x <= &37 / &50 ==> ~linside c s u v a x (&1))
     ==> s * (u + a) + c * (v + a) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--(u + a)`; `--u:real`; `--(v + a)`; `--v:real`;
    `--(c * (&37 / &50) + s)`; `--(c - s * (&37 / &50))`;
    `--(c * (&1 / &5) + s)`; `--(c - s * (&1 / &5))`] CCLSS_SUPPORT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    X_GEN_TAC `w:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(MP (MP (SPEC `(&1 - w) * (&37 / &50) + w * (&1 / &5)` (ASSUME ccc702p_top))
        (REAL_ARITH `w <= &1 ==> &1 / &5 <= (&1 - w) * (&37 / &50) + w * (&1 / &5)`
         |> C MP (ASSUME `w <= &1`)))
        (REAL_ARITH `&0 <= w ==> (&1 - w) * (&37 / &50) + w * (&1 / &5) <= &37 / &50`
         |> C MP (ASSUME `&0 <= w`))) THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: left_support (private) *)
let CCC702P_LEFT_SUPPORT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     c * (-- &6 / &25) + s * (-- &13 / &100) <= u /\
     v < --s * (-- &6 / &25) + c * (-- &13 / &100) /\
     --s * (-- &6 / &25) + c * (-- &13 / &100) < v + a /\
     u < s * (-- &13 / &50) /\ s * (-- &13 / &50) < u + a /\
     c * (-- &13 / &50) <= v /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (-- &6 / &25))
                           ((&1 - w) * (-- &13 / &100) + w * (-- &13 / &50)))
     ==> --(&39 / &625) <= ((&13 / &100) * c + (&6 / &25) * s) * u +
                          ((&6 / &25) * c - (&13 / &100) * s) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real`; `u + a:real`; `v:real`; `v + a:real`;
    `c * (-- &6 / &25) + s * (-- &13 / &100)`; `--s * (-- &6 / &25) + c * (-- &13 / &100)`;
    `s * (-- &13 / &50)`; `c * (-- &13 / &50)`] CCLSS_SUPPORT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    X_GEN_TAC `w:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(MP (MP (SPEC `w:real` (ASSUME ccc702p_left)) (ASSUME `&0 <= w`))
              (ASSUME `w <= &1`)) THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative (private) *)
let CCC702P_NEGATIVE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (-- &43 / &500) (&0) /\ linside c s u v a (&13 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&1 / &2) (&0) /\ ~linside c s u v a (&0) (&1) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (-- &6 / &25))
                           ((&1 - w) * (-- &13 / &100) + w * (-- &13 / &50)))
     ==> linside c s u v a (&3 / &10) (-- &7 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CCC702P_INST_TAC ccc702p_left `&1` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  CCC702P_UNFOLD_TAC THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 * c < &7 * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ASSUME `~linside c (--t) u v a (&1 / &2) (&0)`) THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * (&3 / &10) + --t * (-- &7 / &100) < u + a` ASSUME_TAC THENL
   [ASM_CASES_TAC `&6 * t <= &5 * c` THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCC702P_USE_TAC(SPECL [`c:real`; `t:real`; `&3 / &10`; `&107 / &100`]
      CCOS_INCREASING_PROJECTION) THEN
    CCC702P_NFACT_TAC `~linside c (--t) u v a (&0) (&1)` `v + a <= c` THEN
    CCC702P_NFACT_TAC `~linside c (--t) u v a (&0) (-- &13 / &50)` `c * (-- &13 / &50) <= v` THEN
    CCC702P_USE_TAC(SPECL [`c:real`; `t:real`] CCC702N_NEGATIVE_GAP) THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* the scalar core of the lFace step of positive (Lean: inline nlinarith) *)
let CCC702P_LFACE_SCALAR = prove
 (`forall c s. c pow 2 + s pow 2 = &1 /\ &50 / &63 < c /\ c < &5 / &6 /\
         &14 / &25 < s /\ s <= c
     ==> ((&13 / &100) * c + (&6 / &25) * s) * (c * (&1 / &5) + s) +
         ((&6 / &25) * c - (&13 / &100) * s) * c -
         ((&37 / &100) * c + (&11 / &100) * s) <= --(&39 / &625)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_TAC [SQ_NONNEG `c - s:real`; SQ_NONNEG `s:real`]);;

(* Lean: positive (private) *)
(* LP-based linear arithmetic (cheaper than REAL_ARITH in large contexts) *)
let CCC702P_LIN_TAC =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let CCC702P_LNFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN
    STRIP_TAC THEN CCC702P_LIN_TAC; ALL_TAC];;

let CCC702P_LLE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN CCC702P_LIN_TAC; DISCH_TAC];;

let CCC702P_LLT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN CCC702P_LIN_TAC; DISCH_TAC];;

let CCC702P_LPROJ_TAC th c0 s0 a b =
  let th' = SPECL [`c:real`; `s:real`; c0; s0; a; b] th in
  SUBGOAL_THEN (rand(concl th')) ASSUME_TAC THENL
   [MATCH_MP_TAC th' THEN REWRITE_TAC[REAL_POW_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN CCC702P_LIN_TAC;
    ALL_TAC];;

let CCC702P_LUSE_TAC th' =
  SUBGOAL_THEN (rand(concl th')) ASSUME_TAC THENL
   [MATCH_MP_TAC th' THEN REWRITE_TAC[REAL_POW_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN CCC702P_LIN_TAC;
    ALL_TAC];;

let CCC702P_C_LE_1 = prove
 (`forall c s. c * c + s * s = &1 ==> c <= &1`,
  REPEAT STRIP_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`]);;

let CCC702P_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (-- &43 / &500) (&0) /\ linside c s u v a (&13 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&1 / &2) (&0) /\ ~linside c s u v a (&0) (&1) /\
     (forall x. &1 / &5 <= x ==> x <= &37 / &50 ==> ~linside c s u v a x (&1)) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (-- &6 / &25))
                           ((&1 - w) * (-- &13 / &100) + w * (-- &13 / &50)))
     ==> linside c s u v a (&3 / &10) (-- &7 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CCC702P_INST_TAC ccc702p_top `&1 / &5` THEN
  CCC702P_INST_TAC ccc702p_top `&37 / &50` THEN
  CCC702P_INST_TAC ccc702p_left `&0` THEN
  CCC702P_INST_TAC ccc702p_left `&1` THEN
  CCC702P_UNFOLD_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCC702P_C_LE_1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CCC702P_LNFACT_TAC `~linside c s u v a (&1 / &2) (&0)` `--s * (&1 / &2) <= v` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [CCC702P_LIN_TAC; ALL_TAC] THEN
  CCC702P_LNFACT_TAC `~linside c s u v a (&0) (&1)` `v + a <= c` THEN
  CCC702P_LNFACT_TAC `~linside c s u v a (&37 / &50) (&1)` `u + a <= c * (&37 / &50) + s` THEN
  SUBGOAL_THEN `&9 * c < &13 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCC702P_LNFACT_TAC `~linside c s u v a (&1 / &5) (&1)` `v + a <= c - s * (&1 / &5)` THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCC702P_TOP_SUPPORT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE CCC702P_LIN_TAC); DISCH_TAC] THEN
    CCC702P_LUSE_TAC(SPECL [`c:real`; `s:real`] CCC702N_SHALLOW_MARGIN) THEN
    CCC702P_LLT_MUL_TAC `s:real` `u + a - (c * (&13 / &20) + s * (&7 / &20))` THEN
    CCC702P_LLT_MUL_TAC `c:real` `v + a - (&1 - s * (&1 / &2))` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN CCC702P_LIN_TAC;
    ALL_TAC] THEN
  CCC702P_LUSE_TAC(SPECL [`c:real`; `s:real`] CCC702N_STEEP_BOUNDS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  CCC702P_LPROJ_TAC CCCP_AFTER `&91 / &109` `&60 / &109` `&1` `&3 / &10` THEN
  CCC702P_LNFACT_TAC `~linside c s u v a (&1 / &5) (&1)` `u + a <= c * (&1 / &5) + s` THEN
  CCC702P_LNFACT_TAC `~linside c s u v a (-- &6 / &25) (-- &13 / &100)`
    `c * (-- &6 / &25) + s * (-- &13 / &100) <= u` THEN
  SUBGOAL_THEN `s * (-- &13 / &50) <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    CCC702P_LNFACT_TAC `~linside c s u v a (&0) (-- &13 / &50)` `c * (-- &13 / &50) <= v` THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCC702P_LEFT_SUPPORT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE CCC702P_LIN_TAC); DISCH_TAC] THEN
    CCC702P_LLE_MUL_TAC `(&13 / &100) * c + (&6 / &25) * s` `c * (&1 / &5) + s - (u + a)` THEN
    CCC702P_LLE_MUL_TAC `(&6 / &25) * c - (&13 / &100) * s` `c - (v + a)` THEN
    CCC702P_LLT_MUL_TAC `a - &1` `(&37 / &100) * c + (&11 / &100) * s` THEN
    SUBGOAL_THEN `&50 / &63 < c` ASSUME_TAC THENL [CCC702P_LIN_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`] CCC702P_LFACE_SCALAR) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN CCC702P_LIN_TAC; DISCH_TAC] THEN
    CCC702P_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1900 / &2861) * c < (&2139 / &2861) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCC702P_LPROJ_TAC CCCP_BEFORE `&2139 / &2861` `&1900 / &2861` `&1 / &5` `&63 / &50` THEN
    CCC702P_LIN_TAC;
    ALL_TAC] THEN
  CCC702P_LPROJ_TAC CCCP_AFTER `&2139 / &2861` `&1900 / &2861` `&107 / &100` `&3 / &10` THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN CCC702P_LIN_TAC);;

(* Lean: point *)
let CCC702P_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (-- &43 / &500) (&0) /\ linside c s u v a (&13 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&1 / &2) (&0) /\ ~linside c s u v a (&0) (&1) /\
     (forall x. &1 / &5 <= x ==> x <= &37 / &50 ==> ~linside c s u v a x (&1)) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (-- &6 / &25))
                           ((&1 - w) * (-- &13 / &100) + w * (-- &13 / &50)))
     ==> linside c s u v a (&3 / &10) (-- &7 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC CCC702P_POSITIVE THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) then ASM_MESON_TAC[] g else ASM_REAL_ARITH_TAC g);
    MATCH_MP_TAC CCC702P_NEGATIVE THEN EXISTS_TAC `--sr` THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
    REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) then ASM_MESON_TAC[] g else ASM_REAL_ARITH_TAC g)]);;

(* Lean: point_original *)
let CCC702P_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&1) (&113 / &50) /\
     ~linside c s u v a (&3 / &2) (&2) /\ ~linside c s u v a (&1) (&3) /\
     (forall x. &6 / &5 <= x ==> x <= &87 / &50 ==> ~linside c s u v a x (&3)) /\
     (forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (&19 / &25) + w)
                           ((&1 - w) * (&187 / &100) + w * (&87 / &50)))
     ==> linside c s u v a (&13 / &10) (&193 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &1 + s * &2)`; `v - (--s * &1 + c * &2)`;
                `a:real`] CCC702P_POINT) THEN
  REWRITE_TAC[CCC702P_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN DISCH_TAC THEN
      MP_TAC(SPEC `x + &1`
        (ASSUME `forall x. &6 / &5 <= x ==> x <= &87 / &50 ==> ~linside c s u v a x (&3)`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
      X_GEN_TAC `w:real` THEN DISCH_TAC THEN DISCH_TAC THEN
      MP_TAC(MP (MP (SPEC `w:real` (ASSUME `forall w. &0 <= w ==> w <= &1 ==>
        ~linside c s u v a ((&1 - w) * (&19 / &25) + w)
                           ((&1 - w) * (&187 / &100) + w * (&87 / &50))`))
        (ASSUME `&0 <= w`)) (ASSUME `w <= &1`)) THEN
      REWRITE_TAC[linside] THEN REAL_ARITH_TAC];
    REWRITE_TAC[]]);;
