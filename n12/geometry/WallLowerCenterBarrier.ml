(* ========================================================================= *)
(* Port of Compact/Geometry/WallLowerCenterBarrier.lean (Jatloe, N12-jatloe). *)
(* A lower foreign point on the wall row gives a quantitative centre cut.    *)
(* short_projections: WFP_SHORT_PROJECTIONS (instantiated by WFP_SP);        *)
(* exists_positive_frame: WCB_EXISTS_POSITIVE_FRAME;                         *)
(* positive_frame_wall_bounds: C977WC_POSITIVE_FRAME_WALL_BOUNDS.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

(* Lean: positive_center (private) *)
let WLCB_POSITIVE_CENTER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     &0 <= c * u - s * (v + a) /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&1) (&87 / &50)) /\
     ~(linside c s u v a (&33 / &20) (&47 / &20))
     ==> &21 / &10 < lcy c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside; lcy] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s:real`; SQ_NONNEG `c - s:real`;
                  SQ_NONNEG `s - &1`; SQ_NONNEG `c - &1`]
    [`c <= &1`; `&0 <= c * s`; `&1 <= c + s`; `c + s <= &3 / &2`] THEN
  NLIN_FACTS_TAC [] [`&1 + (&4 / &5) * c * s <= c + s`] THEN
  SUBGOAL_THEN `c * &1 + s * &87 / &50 < u + a /\
                --s * &1 + c * &87 / &50 < v + a` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &1 + s * &87 / &50 <= u \/ --s * &1 + c * &87 / &50 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
  [MP_TAC(WFP_SP `&13 / &20` `&61 / &100`) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   SUBGOAL_THEN `u < c * &33 / &20 + s * &47 / &20 /\
                 --s * &33 / &20 + c * &47 / &20 < v + a` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c * &33 / &20 + s * &47 / &20 < u + a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `--s * &33 / &20 + c * &47 / &20 <= v` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `c - s:real`]
    [`&0 <= s * (u - (c * &1 + s * &87 / &50))`;
     `&0 <= c * (v - (--s * &33 / &20 + c * &47 / &20))`;
     `&0 < (a - &1) * (c + s)`; `s pow 2 <= &1`; `c * s <= &1 / &2`] THEN
   NLIN_TAC [];
   SUBGOAL_THEN `&0 < &1 + s pow 2 + c * s` ASSUME_TAC THENL
   [NLIN_TAC []; ALL_TAC] THEN
   NLIN_FACTS_TAC []
    [`&0 <= s * (c * u - s * (v + a))`;
     `&0 < (a - &1) * (&1 + s pow 2 + c * s)`] THEN
   SUBGOAL_THEN `c * (s * (u + a / &2) + c * (v + a / &2)) =
                 s * (c * u - s * (v + a)) + v + a / &2 * (&1 + s pow 2 + c * s)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (&1 + s pow 2 + c * s) / &2 - s - (&9 / &25) * c`
   ASSUME_TAC THENL
   [ASM_CASES_TAC `s <= &18 / &25` THENL
    [SUBGOAL_THEN `&0 <= (&1 - c) * (&9 / &25 - s / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     NLIN_TAC [SQ_NONNEG `s - &1 / &2`];
     SUBGOAL_THEN `&0 <= c * (s / &2 - &9 / &25)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     NLIN_TAC [SQ_NONNEG `s - &1`]]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < c * ((s * (u + a / &2) + c * (v + a / &2)) - &21 / &10)`
   ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= c * (&21 / &10 - (s * (u + a / &2) + c * (v + a / &2)))`
   MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC]);;

(* Lean: center_above *)
let WLCB_CENTER_ABOVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&1) (&87 / &50)) /\
     ~(linside c s u v a (&33 / &20) (&47 / &20))
     ==> &21 / &10 < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `&21 / &10 < lcy c' s' u' v' a` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC WLCB_POSITIVE_CENTER THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real`; `y:real`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN REAL_ARITH_TAC);;
