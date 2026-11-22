(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/ShorterCornerWall.lean              *)
(* (N12Compact.Completion.OtherCases.ShorterCornerWall).  The genuine right  *)
(* wall and the shorter corner reach exclude the three forced near-wall      *)
(* points.  Square q is c s u v a.  ShorterCornerScalars.margin is           *)
(* OSCS_MARGIN; increasing_projection is CCOS_INCREASING_PROJECTION;          *)
(* CanonicalProjection.after is CCCP_AFTER; canonical_frame is               *)
(* CLF_CANONICAL_FRAME; DerivedWalls / vertex are OCDW_* / OCWPVG_VERTEX.    *)
(* Tag OCSCW_.                                                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_ShorterCornerScalars.ml";;
needs "n12/geometry/CP_OtherCases_DerivedWalls.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let OCSCW_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

let OCSCW_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: positive (private) *)
let OCSCW_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     (forall x y. linside c s u v a x y ==> x <= &1) /\
     linside c s u v a (&43 / &500) (&0) /\ linside c s u v a (&0) (&4 / &5) /\
     ~linside c s u v a (&1 / &50) (&0) /\ ~linside c s u v a (&11 / &50) (&1)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (&43 / &500) (&0)`; `linside c s u v a (&0) (&4 / &5)`] THEN
  SUBGOAL_THEN `c * (&1 / &50) <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCSCW_MISS_TAC `~linside c s u v a (&1 / &50) (&0)`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&1 / &5`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN `v + a <= --s * (&11 / &50) + c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCSCW_MISS_TAC `~linside c s u v a (&11 / &50) (&1)`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `u + a`; `v:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--(&1)`; `&0`; `--(&1)`;
                `&43 / &500`; `&0`; `c * (u + a) - s * v`; `s * (u + a) + c * v`]
    OCDW_CLOSED_AFFINE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o check (fun th -> is_forall(concl th)
      && length(fst(strip_forall(concl th))) = 2 && is_imp(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OSCS_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  OCSCW_PROD_TAC
   [`&0 <= c * (u - (&1 / &50) * c)`;
    `&0 <= s * (c - (&11 / &50) * s - (v + a))`;
    `&0 < (a - &1) * (c + s)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC);;

(* Lean: negative (private) *)
let OCSCW_NEGATIVE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&43 / &500) (&0) /\ linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&0) (&4 / &5) /\
     ~linside c s u v a (&1 / &50) (&0) /\
     ~linside c s u v a (&1 / &50) (&1 / &50) /\
     ~linside c s u v a (--(&1 / &25)) (&11 / &100) /\
     ~linside c s u v a (&11 / &50) (&1)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c (--t) u v a (&43 / &500) (&0)`; `linside c (--t) u v a (&0) (&13 / &50)`;
    `linside c (--t) u v a (&0) (&4 / &5)`] THEN
  SUBGOAL_THEN `t * (&1 / &50) <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCSCW_MISS_TAC `~linside c (--t) u v a (&1 / &50) (&0)`; ALL_TAC] THEN
  ASM_CASES_TAC `&5 * c <= &6 * t` THENL
   [SUBGOAL_THEN `v + a <= t * (&11 / &50) + c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      OCSCW_MISS_TAC `~linside c (--t) u v a (&11 / &50) (&1)`; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `t:real`; `&4 / &5`; `&3 / &5`; `&1`; `&1 / &5`] CCCP_AFTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    RASM_ARITH_TAC;
    ASM_CASES_TAC `&4 * t <= c` THENL
     [UNDISCH_TAC `~linside c (--t) u v a (&1 / &50) (&1 / &50)` THEN REWRITE_TAC[] THEN
      REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
      UNDISCH_TAC `~linside c (--t) u v a (--(&1 / &25)) (&11 / &100)` THEN REWRITE_TAC[] THEN
      REWRITE_TAC[linside] THEN RASM_ARITH_TAC]]);;

(* Lean: impossible *)
let OCSCW_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> x <= &1) /\
     linside c s u v a (&43 / &500) (&0) /\ linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&0) (&4 / &5) /\
     ~linside c s u v a (&1 / &50) (&0) /\
     ~linside c s u v a (&1 / &50) (&1 / &50) /\
     ~linside c s u v a (--(&1 / &25)) (&11 / &100) /\
     ~linside c s u v a (&11 / &50) (&1)
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
   [MATCH_MP_TAC OCSCW_POSITIVE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OCSCW_NEGATIVE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`; `--sr`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;
