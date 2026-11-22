(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/UpperBarPoint.lean                  *)
(* (namespace N12Compact.Completion.OtherCases.UpperBarPoint).  The upper   *)
(* square reaches the sharp common point.  short_projections: WFP_SP;       *)
(* increasing_projection: CCOS_INCREASING_PROJECTION; CanonicalScalars.     *)
(* bounds: CCCS_BOUNDS; SharpPointScalars.arc / upper_lower_v: OCSPS_*;     *)
(* WallProfile.vertex: OCWPVG_VERTEX; SharpBarGeometry.vertical_crossing:   *)
(* OCSBG_VERTICAL_CROSSING; canonical_frame: CLF_CANONICAL_FRAME.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;
needs "n12/geometry/CP_OtherCases_SharpBarGeometry.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let OCUBP_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* t by contradiction, using only the omitted points in keep *)
let OCUBP_STEP t keep =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCUBP_KEEP_TAC keep; ALL_TAC];;

(* Lean: negative_point (private) *)
let OCUBP_NEGATIVE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&2 / &5) (&1) /\
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
  OCUBP_STEP `s <= u` [mP0] THEN
  OCUBP_STEP `--s * &21 / &40 + c * &1 / &8 <= v` [mY] THEN
  OCUBP_STEP `u + a <= c + s` [mP1] THEN
  OCUBP_KEEP_TAC []);;

(* Lean: positive_point (private) *)
let OCUBP_POSITIVE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&2 / &5) (&1) /\
      ~linside c s u v a (&0) (&13 / &50) /\
      ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&1) (&1) /\
      (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  let mY = `~linside c s u v a (&21 / &40) (&1 / &8)`
  and mL = `~linside c s u v a (&0) (&13 / &50)`
  and mP0 = `~linside c s u v a (&0) (&1)`
  and mP1 = `~linside c s u v a (&1) (&1)`
  and mB0 = `~linside c s u v a (&1) (&13 / &50)`
  and mB1 = `~linside c s u v a (&1) (&14 / &25)` in
  MAP_EVERY (fun y -> FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[] o
      CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_LE_CONV) o SPEC y o check (is_forall o concl)))
    [`&13 / &50`; `&14 / &25`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&19 / &40`; `&7 / &8`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(WFP_SP `&19 / &40` `&27 / &200`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `u < c * &21 / &40 + s * &1 / &8` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCUBP_STEP `v + a <= --s + c` [mP1] THEN
    OCUBP_STEP `--s + c * &13 / &50 <= v` [mB0] THEN
    OCUBP_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c * &21 / &40 + s * &1 / &8 < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCUBP_STEP `v + a <= c` [mP0] THEN
    OCUBP_STEP `s * &13 / &50 <= u` [mL] THEN
    OCUBP_KEEP_TAC []; ALL_TAC] THEN
  OCUBP_STEP `--s * &21 / &40 + c * &1 / &8 <= v` [mY] THEN
  OCUBP_STEP `u + a <= c + s` [mP1] THEN
  OCUBP_STEP `v + a <= c` [mP0] THEN
  OCUBP_STEP `s * &13 / &50 <= u` [mL] THEN
  OCUBP_STEP `--s + c * &13 / &50 <= v` [mB0] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [OCUBP_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < &11 / &25 * c + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCUBP_STEP `u + a <= c + s * &14 / &25` [mB1] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                  `u + a`; `v:real`] OCWPVG_VERTEX) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OCSPS_ARC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `&0 <= c * s /\ &0 <= c * (u - s * &13 / &50) /\ &0 <= s * (c - (v + a)) /\
      &0 < (a - &1) * (c + s) /\ &0 <= s * (u - s * &13 / &50) /\
      &0 <= c * (v - (--s + c * &13 / &50)) /\ &0 < s * (a - c) /\
      &0 <= s * ((c + s * &14 / &25) - (u + a)) /\ &0 <= c * (c - (v + a)) /\
      &0 < c * (a - (&11 / &25 * c + s))` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
        MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
        MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
        MATCH_MP_TAC REAL_LT_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OCSBG_VERTICAL_CROSSING THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
      `c * (u + a) - s * v`; `s * (u + a) + c * v`; `&7 / &20`; `&7 / &20`;
      `&1`; `&13 / &50`; `&14 / &25`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSPS_UPPER_LOWER_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  OCUBP_KEEP_TAC []);;

(* Lean: point *)
let OCUBP_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&2 / &5) (&1) /\
      ~linside c s u v a (&0) (&13 / &50) /\
      ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&1) (&1) /\
      (forall y. &13 / &50 <= y ==> y <= &14 / &25 ==> ~linside c s u v a (&1) y)
      ==> linside c s u v a (&21 / &40) (&1 / &8)`,
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
   [MATCH_MP_TAC OCUBP_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OCUBP_NEGATIVE_POINT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCUBP_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: point_original *)
let OCUBP_POINT_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&47 / &20) (&47 / &20) /\
      linside c s u v a (&12 / &5) (&3) /\
      ~linside c s u v a (&2) (&113 / &50) /\
      ~linside c s u v a (&2) (&3) /\ ~linside c s u v a (&3) (&3) /\
      (forall y. &113 / &50 <= y ==> y <= &64 / &25 ==> ~linside c s u v a (&3) y)
      ==> linside c s u v a (&101 / &40) (&17 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCUBP_POINT) THEN
  REWRITE_TAC[OCUBP_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
  ASM_REAL_ARITH_TAC);;
