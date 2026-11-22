(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OutwardBarPoint.lean                *)
(* (namespace N12Compact.Completion.OtherCases.OutwardBarPoint).  The full  *)
(* outward bar forces a sharp strict point and its support faces.           *)
(* SharpPointScalars.arc / outward_short_u / outward_lower_u / _v: OCSPS_*; *)
(* WallProfile.vertex: OCWPVG_VERTEX; SharpBarGeometry.horizontal_crossing: *)
(* OCSBG_HORIZONTAL_CROSSING; C981CompletionOutwardAnchor.                  *)
(* nonnegative_impossible: C981OA_NONNEGATIVE_IMPOSSIBLE; pullY:            *)
(* LINSIDE_PULLY; canonical_frame: CLF_CANONICAL_FRAME.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;
needs "n12/geometry/CP_OtherCases_SharpBarGeometry.ml";;
needs "n12/geometry/CP_C981_OutwardAnchor.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let OCOBP_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let OCOBP_STEP t keep =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCOBP_KEEP_TAC keep; ALL_TAC];;

(* Lean: Faces (structure) *)
let ocobp_faces = new_definition
 `ocobp_faces (c:real) s u v a <=>
    &13 / &50 * c <= u /\
    --(&543 / &500) * s <= v /\
    u + a <= c + s /\
    v + a <= c - &4 / &5 * s /\
    &0 < s /\
    &1 < c + &143 / &500 * s /\
    &1 < &37 / &50 * c + s`;;

(* Lean: positive_faces *)
let OCOBP_POSITIVE_FACES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&1) (&13 / &50) /\
      ~linside c s u v a (&13 / &50) (&0) /\
      ~linside c s u v a (&543 / &500) (&0) /\
      ~linside c s u v a (&1) (&1) /\
      ~linside c s u v a (&543 / &500) (&1) /\
      (forall z. &13 / &50 <= z ==> z <= &4 / &5 ==> ~linside c s u v a z (&1))
      ==> ocobp_faces c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let mG = `~linside c s u v a (&13 / &50) (&0)`
  and mR = `~linside c s u v a (&543 / &500) (&0)`
  and mP = `~linside c s u v a (&1) (&1)`
  and mH = `~linside c s u v a (&543 / &500) (&1)`
  and mF = `~linside c s u v a (&13 / &50) (&1)`
  and mT = `~linside c s u v a (&4 / &5) (&1)` in
  MAP_EVERY (fun z -> FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[] o
      CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_LE_CONV) o SPEC z o check (is_forall o concl)))
    [`&13 / &50`; `&4 / &5`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `v < --s * &13 / &50` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCOBP_STEP `c * &13 / &50 + s <= u` [mF] THEN
    OCOBP_STEP `u + a <= c * &4 / &5 + s` [mT] THEN
    OCOBP_KEEP_TAC []; ALL_TAC] THEN
  OCOBP_STEP `c * &13 / &50 <= u` [mG] THEN
  OCOBP_STEP `--s * &543 / &500 <= v` [mR] THEN
  OCOBP_STEP `u + a <= c * &543 / &500 + s` [mH] THEN
  SUBGOAL_THEN `&87 / &500 < s` ASSUME_TAC THENL [OCOBP_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c + &43 / &500 * s < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < s * (s - &43 / &250)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `c - &1` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  OCOBP_STEP `u + a <= c + s` [mP] THEN
  OCOBP_STEP `v + a <= --s * &13 / &50 + c` [mF] THEN
  SUBGOAL_THEN `&1 < c + &143 / &500 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCOBP_STEP `u + a <= c * &4 / &5 + s` [mT] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                  `u + a`; `v + a`] OCWPVG_VERTEX) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OCSPS_ARC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN
     `&0 < c * (a - s) /\ &0 <= c * (u - c * &13 / &50) /\
      &0 <= s * ((--s * &13 / &50 + c) - (v + a)) /\
      &0 <= c * ((c * &4 / &5 + s) - (u + a)) /\ &0 <= s * (v - --s * &543 / &500) /\
      &0 < s * (a - (c + &143 / &500 * s)) /\ &0 < (a - &1) * (c + s) /\
      &0 <= s * (u - c * &13 / &50) /\ &0 <= c * (v - --s * &543 / &500)`
      STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
        MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL;
        MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OCSBG_HORIZONTAL_CROSSING THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
      `c * (u + a) - s * (v + a)`; `s * (u + a) + c * (v + a)`; `&7 / &20`; `&7 / &20`;
      `&1`; `&13 / &50`; `&4 / &5`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSPS_OUTWARD_SHORT_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  OCOBP_STEP `v + a <= --s * &4 / &5 + c` [mT] THEN
  REWRITE_TAC[ocobp_faces] THEN OCOBP_KEEP_TAC []);;

(* Lean: positive_point *)
let OCOBP_POSITIVE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      linside c s u v a (&1) (&13 / &50) /\
      ~linside c s u v a (&13 / &50) (&0) /\
      ~linside c s u v a (&543 / &500) (&0) /\
      ~linside c s u v a (&1) (&1) /\
      ~linside c s u v a (&543 / &500) (&1) /\
      (forall z. &13 / &50 <= z ==> z <= &4 / &5 ==> ~linside c s u v a z (&1))
      ==> linside c s u v a (&21 / &40) (--(&1 / &8))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCOBP_POSITIVE_FACES) THEN ASM_REWRITE_TAC[ocobp_faces] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSPS_OUTWARD_LOWER_U) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSPS_OUTWARD_LOWER_V) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT DISCH_TAC THEN
  OCOBP_KEEP_TAC []);;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let OCOBP_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_point_original *)
let OCOBP_POSITIVE_POINT_ORIGINAL = prove
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
      ==> linside c s u v a (&101 / &40) (&15 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCOBP_POSITIVE_POINT) THEN
  REWRITE_TAC[OCOBP_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: point_original *)
let OCOBP_POINT_ORIGINAL = prove
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
      ==> linside c s u v a (&101 / &40) (&15 / &8)`,
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
   [MATCH_MP_TAC OCOBP_POSITIVE_POINT_ORIGINAL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
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
