(* ========================================================================= *)
(* Port of Compact/Geometry/WallCenterBarrier.lean                           *)
(* (with S12.exists_positive_frame from source/S12/WallGeometry.lean).       *)
(* short_projections: WFP_SHORT_PROJECTIONS (instantiated by WFP_SP);        *)
(* positive_frame_wall_bounds: C977WC_POSITIVE_FRAME_WALL_BOUNDS.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/C977WallChains.ml";;

(* Lean: S12.exists_positive_frame *)
let WCB_EXISTS_POSITIVE_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 <= c' /\ &0 <= s' /\ a' = a /\
           lcx c' s' u' v' a' = lcx c s u v a /\ lcy c' s' u' v' a' = lcy c s u v a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)`,
  let tac wits = MAP_EVERY EXISTS_TAC wits THEN
    REWRITE_TAC[linside; lcx; lcy] THEN REPEAT CONJ_TAC THEN
    REPEAT GEN_TAC THEN ASM_REAL_ARITH_TAC in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= c` THEN ASM_CASES_TAC `&0 <= s` THENL
   [tac [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`];
    tac [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`];
    tac [`s:real`; `--c:real`; `--v - a:real`; `u:real`; `a:real`];
    tac [`--c:real`; `--s:real`; `--u - a:real`; `--v - a:real`; `a:real`]]);;

(* Lean: positive_center (private) *)
let WCB_POSITIVE_CENTER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     &0 <= c * u - s * (v + a) /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&19 / &25) (&187 / &100)) /\
     ~(linside c s u v a (&87 / &50) (&2))
     ==> &2 < lcy c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside; lcy] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s:real`; SQ_NONNEG `c - s:real`;
                  SQ_NONNEG `s - &1`; SQ_NONNEG `c - &1`]
    [`s <= &1`; `c <= &1`; `&0 <= c * s`; `&1 <= c + s`; `c + s <= &3 / &2`] THEN
  NLIN_FACTS_TAC [] [`&1 + (&4 / &5) * c * s <= c + s`] THEN
  MP_TAC(WFP_SP `&49 / &50` `&13 / &100`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `u + a <= c * &87 / &50 + s * &2 \/ --s * &87 / &50 + c * &2 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--s * &19 / &25 + c * &187 / &100 < v + a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &19 / &25 + s * &187 / &100 <= u \/ --s * &19 / &25 + c * &187 / &100 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `--s * &87 / &50 + c * &2 <= v` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `c - s:real`; SQ_NONNEG `c:real`]
     [`&0 <= s * (u - (c * &19 / &25 + s * &187 / &100))`;
      `&0 <= c * (v - (--s * &87 / &50 + c * &2))`;
      `&0 < (a - &1) * (c + s)`; `s pow 2 <= &1`; `c * s <= &1 / &2`] THEN
    NLIN_TAC [];
    NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
     [`&0 <= s * (c * u - s * (v + a))`;
      `&0 < (a - &1) * (&1 + s pow 2 + c * s)`] THEN
    SUBGOAL_THEN `&0 < c * ((s * (u + a / &2) + c * (v + a / &2)) - &2)` ASSUME_TAC THENL
     [NLIN_TAC [SQ_NONNEG `s - &19 / &25`]; ALL_TAC] THEN
    NLIN_TAC []]);;

(* Lean: center_above *)
let WCB_CENTER_ABOVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&19 / &25) (&187 / &100)) /\
     ~(linside c s u v a (&87 / &50) (&2))
     ==> &2 < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `&2 < lcy c' s' u' v' a` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC WCB_POSITIVE_CENTER THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real`; `y:real`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN REAL_ARITH_TAC);;
