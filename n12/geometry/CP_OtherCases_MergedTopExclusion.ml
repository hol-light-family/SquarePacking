(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedTopExclusion.lean             *)
(* (N12Compact.Completion.OtherCases.MergedTopExclusion).  The full          *)
(* merged-top obstruction using the actual excluded segment.  Square q is    *)
(* c s u v a.  canonical_frame is CLF_CANONICAL_FRAME; DerivedWalls lemmas   *)
(* are OCDW_*; WallProfile.vertex is OCWPVG_VERTEX; MergedTopScalars lemmas  *)
(* are OCMTS_*.  Tag OCMTE_.                                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_OtherCases_DerivedWalls.ml";;
needs "n12/geometry/CP_OtherCases_MergedTopScalars.ml";;

let OCMTE_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

let OCMTE_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: positive (private) *)
let OCMTE_POSITIVE = prove
 (`forall c s u v a.
     &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&33 / &20) (&33 / &20) /\ linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&47 / &20) (&47 / &20) /\ ~linside c s u v a (&1) (&12 / &5)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (&33 / &20) (&33 / &20)`; `linside c s u v a (&8 / &5) (&3)`] THEN
  SUBGOAL_THEN `u + a <= c * (&47 / &20) + s * (&47 / &20)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCMTE_MISS_TAC `~linside c s u v a (&47 / &20) (&47 / &20)`; ALL_TAC] THEN
  SUBGOAL_THEN `c + s * (&12 / &5) <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCMTE_MISS_TAC `~linside c s u v a (&1) (&12 / &5)`; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative (private) *)
let OCMTE_NEGATIVE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &0 < c /\ &0 <= t /\ t <= c /\ &1 < a /\ a <= &1001 / &1000 /\
     linside c s u v a (&33 / &20) (&33 / &20) /\ linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&47 / &20) (&47 / &20) /\
     (forall y. &113 / &50 <= y ==> y <= &12 / &5 ==> ~linside c s u v a (&1) y)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c (--t) u v a (&33 / &20) (&33 / &20)`; `linside c (--t) u v a (&8 / &5) (&3)`] THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&27 / &20 * c - &1 / &20 * t < &1001 / &1000` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] OCMTS_STEEP_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the vertical line x = 1 is avoided *)
  SUBGOAL_THEN `forall y. ~linside c (--t) u v a (&1) y` ASSUME_TAC THENL
   [SUBGOAL_THEN `c - t * (&12 / &5) <= u /\ t + c * (&113 / &50) <= v`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `&12 / &5` o check (is_forall o concl));
        FIRST_ASSUM(MP_TAC o SPEC `&113 / &50` o check (is_forall o concl))] THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
      ASM_REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    MP_TAC(ASSUME `linside c (--t) u v a (&1) y`) THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&113 / &50 < y /\ y < &12 / &5` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
       [OCMTE_PROD_TAC [`&0 <= c * (&113 / &50 - y)`];
        OCMTE_PROD_TAC [`&0 <= t * (y - &12 / &5)`]] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t:real`; `u:real`; `v:real`; `a:real`;
                `&33 / &20`; `&33 / &20`; `&1`] OCDW_VERTICAL_RIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t:real`; `u:real`; `v:real`; `a:real`; `u:real`; `v:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t:real`; `u:real`; `v:real`; `a:real`; `&1`; `&0`; `&1`;
                `&33 / &20`; `&33 / &20`; `c * u - --t * v`; `--t * u + c * v`]
    OCDW_CLOSED_AFFINE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] OCMTS_U_MARGIN) THEN
  MP_TAC(SPECL [`c:real`; `t:real`] OCMTS_V_MARGIN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `~linside c (--t) u v a (&47 / &20) (&47 / &20)` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[linside] THEN
  SUBGOAL_THEN `c * (&47 / &20) + --t * (&47 / &20) < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCMTE_PROD_TAC
     [`&0 <= c * ((c * (&47 / &20) + --t * (&47 / &20)) - (u + a))`;
      `&0 < t * ((--(--t) * &33 / &20 + c * &33 / &20) - v)`;
      `&0 < c * (a - &1)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(--t) * (&47 / &20) + c * (&47 / &20) < v + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCMTE_PROD_TAC
     [`&0 <= t * ((--(--t) * (&47 / &20) + c * (&47 / &20)) - (v + a))`;
      `&0 < c * ((c * &8 / &5 + --t * &3) - u)`;
      `&0 < t * (a - &1)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: impossible *)
let OCMTE_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ a <= &1001 / &1000 /\
     linside c s u v a (&33 / &20) (&33 / &20) /\ linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&47 / &20) (&47 / &20) /\
     (forall y. &113 / &50 <= y ==> y <= &12 / &5 ==> ~linside c s u v a (&1) y)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cr:real` (X_CHOOSE_THEN `sr:real` (X_CHOOSE_THEN `ur:real`
    (X_CHOOSE_THEN `vr:real` (X_CHOOSE_THEN `ar:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ar:real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) &&
     is_iff(snd(strip_forall(concl th))) then
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC OCMTE_POSITIVE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&12 / &5` o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];
    MATCH_MP_TAC OCMTE_NEGATIVE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`; `--sr`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;
