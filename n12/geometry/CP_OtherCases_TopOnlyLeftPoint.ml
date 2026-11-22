(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/TopOnlyLeftPoint.lean               *)
(* (namespace N12Compact.Completion.OtherCases.TopOnlyLeftPoint).  Face     *)
(* bounds from strict anchors and omitted endpoints plus one foreign bar.   *)
(* SharpPointScalars.arc / half_lower / half_after: OCSPS_*; WallProfile.   *)
(* vertex: OCWPVG_VERTEX; SharpBarGeometry.vertical_crossing:               *)
(* OCSBG_VERTICAL_CROSSING; increasing_projection:                          *)
(* CCOS_INCREASING_PROJECTION; CanonicalProjection.after: CCCP_AFTER;       *)
(* canonical_frame: CLF_CANONICAL_FRAME.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;
needs "n12/geometry/CP_OtherCases_SharpBarGeometry.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let OCTOLP_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let OCTOLP_STEP t keep =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCTOLP_KEEP_TAC keep; ALL_TAC];;

let OCTOLP_SPEC_TAC ys =
  MAP_EVERY (fun y -> FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[] o
      CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_LE_CONV) o SPEC y o check (is_forall o concl)))
    ys;;

let OCTOLP_CU_TAC = NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`];;

(* Lean: positive_faces *)
let OCTOLP_POSITIVE_FACES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1) /\
      ~linside c s u v a (&1) (&1) /\ ~linside c s u v a (&1) (&13 / &50)
      ==> &13 / &50 * s <= u /\ --s + &13 / &50 * c <= v /\
          u + a <= c + s /\ v + a <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCTOLP_CU_TAC THEN
  let mL = `~linside c s u v a (&0) (&13 / &50)`
  and mP = `~linside c s u v a (&0) (&1)`
  and mC = `~linside c s u v a (&1) (&1)`
  and mB = `~linside c s u v a (&1) (&13 / &50)` in
  SUBGOAL_THEN `v < c * &13 / &50` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCTOLP_STEP `s <= u` [mP] THEN
    OCTOLP_STEP `v + a <= --s + c` [mC] THEN
    OCTOLP_KEEP_TAC []; ALL_TAC] THEN
  OCTOLP_STEP `s * &13 / &50 <= u` [mL] THEN
  OCTOLP_STEP `--s + c * &13 / &50 <= v` [mB] THEN
  OCTOLP_STEP `u + a <= c + s` [mC] THEN
  OCTOLP_STEP `v + a <= c` [mP] THEN
  OCTOLP_KEEP_TAC []);;

(* Lean: bar_face *)
let OCTOLP_BAR_FACE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      &13 / &50 * s <= u /\ --s + &13 / &50 * c <= v /\ v + a <= c /\
      (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
      ==> --s + &14 / &25 * c <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCTOLP_CU_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  OCTOLP_SPEC_TAC [`&14 / &25`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  OCTOLP_STEP `u + a <= c + s * &14 / &25` [`~linside c s u v a (&1) (&14 / &25)`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `u + a`; `v:real`] OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSPS_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= c * s /\ &0 <= c * (u - &13 / &50 * s) /\ &0 <= s * (c - (v + a)) /\
    &0 < (a - &1) * (c + s) /\ &0 <= s * (u - &13 / &50 * s) /\
    &0 <= c * (v - (--s + &13 / &50 * c)) /\ &0 < s * (a - c) /\
    &0 <= s * ((c + s * &14 / &25) - (u + a)) /\
    &0 < c * ((--s + &14 / &25 * c) - v)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
      MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
      MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC OCSBG_VERTICAL_CROSSING THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
    `c * (u + a) - s * v`; `s * (u + a) + c * v`; `&7 / &20`; `&7 / &20`;
    `&1`; `&13 / &50`; `&14 / &25`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: positive (private) *)
let OCTOLP_POSITIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1) /\
      ~linside c s u v a (&1) (&1) /\
      (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
      ==> linside c s u v a (&0) (&31 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OCTOLP_SPEC_TAC [`&13 / &50`] THEN
  MP_TAC(SPEC_ALL OCTOLP_POSITIVE_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCTOLP_BAR_FACE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&11 / &25`] OCSPS_HALF_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&275 / &373`; `&252 / &373`; `&7 / &18`]
    OCSPS_HALF_AFTER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&275 / &373`; `&252 / &373`; `&1`; `&19 / &50`]
    CCCP_AFTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
                  ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN DISCH_TAC THEN
  OCTOLP_KEEP_TAC []);;

(* Lean: negative_faces *)
let OCTOLP_NEGATIVE_FACES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&13 / &50) (&1) /\
      linside c s u v a (&21 / &40) (&1 / &8) /\
      ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1) /\
      ~linside c s u v a (&1) (&1) /\
      (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
      ==> s <= u /\ &13 / &50 * c <= v /\
          u + a <= c + &14 / &25 * s /\ v + a <= c - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCTOLP_CU_TAC THEN
  OCTOLP_SPEC_TAC [`&13 / &50`; `&14 / &25`] THEN
  MP_TAC(SPECL [`c:real`; `--s`; `&3 / &10`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  let mL = `~linside c s u v a (&0) (&13 / &50)`
  and mP = `~linside c s u v a (&0) (&1)`
  and mC = `~linside c s u v a (&1) (&1)`
  and mB0 = `~linside c s u v a (&1) (&13 / &50)`
  and mB1 = `~linside c s u v a (&1) (&14 / &25)` in
  OCTOLP_STEP `s <= u` [mP] THEN
  OCTOLP_STEP `u + a <= c + s * &13 / &50` [mB0] THEN
  OCTOLP_STEP `c * &13 / &50 <= v` [mL] THEN
  OCTOLP_STEP `v + a <= --s + c` [mC] THEN
  OCTOLP_STEP `u + a <= c + s * &14 / &25` [mB1] THEN
  OCTOLP_KEEP_TAC []);;

(* Lean: negative (private) *)
let OCTOLP_NEGATIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&13 / &50) (&1) /\
      linside c s u v a (&21 / &40) (&1 / &8) /\
      ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1) /\
      ~linside c s u v a (&1) (&1) /\
      (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
      ==> linside c s u v a (&0) (&31 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCTOLP_NEGATIVE_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  OCTOLP_CU_TAC THEN
  SUBGOAL_THEN `&13 / &50 < --s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c - &3 / &50 * s < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < --s * (--s - &3 / &25)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `c - &1` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s`; `&19 / &50`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  OCTOLP_KEEP_TAC []);;

(* Lean: point *)
let OCTOLP_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&13 / &50) (&1) /\
      linside c s u v a (&21 / &40) (&1 / &8) /\
      ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1) /\
      ~linside c s u v a (&1) (&1) /\
      (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
      ==> linside c s u v a (&0) (&31 / &50)`,
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
   [MATCH_MP_TAC OCTOLP_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OCTOLP_NEGATIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCTOLP_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: point_original *)
let OCTOLP_POINT_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&47 / &20) (&47 / &20) /\
      linside c s u v a (&113 / &50) (&3) /\
      linside c s u v a (&101 / &40) (&17 / &8) /\
      ~linside c s u v a (&2) (&113 / &50) /\ ~linside c s u v a (&2) (&3) /\
      ~linside c s u v a (&3) (&3) /\
      (forall y. &113 / &50 <= y ==> y <= &64 / &25 ==> ~linside c s u v a (&3) y)
      ==> linside c s u v a (&2) (&131 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCTOLP_POINT) THEN
  REWRITE_TAC[OCTOLP_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
  ASM_REAL_ARITH_TAC);;
