(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/TwoChordHull.lean                   *)
(* (namespace N12Compact.Completion.OtherCases.TwoChordHull).  Two genuine  *)
(* short chords force three strict points on the far side.  Faces:          *)
(* octcf_faces / OCTCF_POSITIVE; CanonicalProjection.after: CCCP_AFTER;     *)
(* increasing_projection: CCOS_INCREASING_PROJECTION; CanonicalScalars.     *)
(* bounds: CCCS_BOUNDS; SegmentCorner.crossing_order: SEGC_CROSSING_ORDER;  *)
(* canonical_frame: CLF_CANONICAL_FRAME.  The Lean reflection               *)
(* pullY (r.translated 0 (-4)) is the square (c, --s, u, --v - a, a).        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_TwoChordFaces.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/SegmentCorner.ml";;

(* Lean: positive_point (private) *)
let OCTCH_POSITIVE_POINT = prove
 (`forall c s u v a x y.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\ octcf_faces c s u v a /\
      &7 / &20 <= x /\ &0 <= y /\ y < &7 / &20 /\ &7 / &10 < x + y /\
      y <= &13 / &50 /\ &13 / &50 - y <= x /\
      (x + &13 / &50 - y) * (&99 / &140) < &1 /\
      (y + &13 / &50) * (&325 / &397) <= x * (&228 / &397) /\
      x * (&325 / &397) + (y + &13 / &50) * (&228 / &397) < &1
      ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[octcf_faces] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&325 / &397`; `&228 / &397`;
                `x:real`; `y + &13 / &50`] CCCP_AFTER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &50 - y`; `x:real`]
    CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < c * (x + y - &7 / &10) /\ &0 <= (c - s) * (&7 / &20 - y) /\
                &0 < c * (&7 / &20 - y) /\ &0 <= s * (x - &7 / &20)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL;
      MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `linside c s u v a (&7 / &20) (&7 / &20)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: positive_points (private) *)
let OCTCH_POSITIVE_POINTS = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (&7 / &20) /\ octcf_faces c s u v a
      ==> linside c s u v a (&51 / &50) (&0) /\
          linside c s u v a (&51 / &50) (&1 / &50) /\
          linside c s u v a (&24 / &25) (&11 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC OCTCH_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: negative_segment_impossible (private) *)
let OCTCH_NEGATIVE_SEGMENT_IMPOSSIBLE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&7 / &20) (&7 / &20) /\ octcf_faces c s u v a /\
      (forall z. &0 <= z ==> z <= &1 ==>
           ~linside c s u v a ((&1 - z) * (&543 / &500) + z) (--(z * (&13 / &50))))
      ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[octcf_faces] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    REWRITE_RULE[REAL_SUB_RZERO; REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID; REAL_NEG_0] o
    CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) o SPEC `&0` o
    check (is_forall o concl)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &50`; `&543 / &500`]
    CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN `u + a <= c * &543 / &500` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c s u v a (&543 / &500) (&0)` THEN REWRITE_TAC[linside] THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
    UNDISCH_TAC `linside c s u v a (&7 / &20) (--(&7 / &20))` THEN
    UNDISCH_TAC `linside c s u v a (&7 / &20) (&7 / &20)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`--(u + a)`; `--u`; `--(v + a)`; `--v`;
                `--(c * &543 / &500)`; `s * &543 / &500`;
                `--(c - s * &13 / &50)`; `s + c * &13 / &50`] SEGC_CROSSING_ORDER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `linside c s u v a (&7 / &20) (&7 / &20)` THEN
      REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
      UNDISCH_TAC `linside c s u v a (&7 / &20) (&7 / &20)` THEN
      REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[linside] THEN
      MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN
      REPEAT STRIP_TAC THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REAL_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(&13 / &50 * c - &43 / &500 * s) * (u + a) -
                (&13 / &50 * s + &43 / &500 * c) * v <= &13 / &50 * &543 / &500`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&12 / &25 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&13 / &50 * c - &43 / &500 * s) * (u + &13 / &50 * s) /\
    &0 <= (&13 / &50 * s + &43 / &500 * c) * (&13 / &50 * c - (v + a)) /\
    &0 < (a - &1) * ((&13 / &50 + &43 / &500) * c + (&13 / &50 - &43 / &500) * s) /\
    &0 <= (c - s) * (&1 - &13 / &50 * (c + s)) /\
    &0 < (c - &7 / &10) * s` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL;
      MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&43 / &500 < &7 / &25 * c * s` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: points *)
let OCTCH_POINTS = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      ~linside c s u v a (&0) (--(&13 / &50)) /\
      ~linside c s u v a (&0) (&13 / &50) /\
      ~linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&1) (&13 / &50) /\
      (forall z. &0 <= z ==> z <= &1 ==>
           ~linside c s u v a ((&1 - z) * (&543 / &500) + z) (z * (&13 / &50)))
      ==> linside c s u v a (&51 / &50) (&0) /\
          linside c s u v a (&51 / &50) (&1 / &50) /\
          linside c s u v a (&24 / &25) (&11 / &100)`,
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
   [MATCH_MP_TAC OCTCH_POSITIVE_POINTS THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OCTCF_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    SUBGOAL_THEN `forall x y. linside c1 (--s1) u1 (--v1 - a) a x y <=>
                        linside c1 s1 u1 v1 a x (--y)` ASSUME_TAC THENL
     [REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c1:real`; `--s1`; `u1:real`; `--v1 - a`; `a:real`]
      OCTCF_POSITIVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
      REWRITE_TAC[REAL_NEG_NEG; REAL_NEG_0] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MATCH_MP_TAC OCTCH_NEGATIVE_SEGMENT_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `--s1`; `u1:real`; `--v1 - a`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[]]);;
