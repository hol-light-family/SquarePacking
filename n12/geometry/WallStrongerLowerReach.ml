(* ========================================================================= *)
(* Port of Compact/Geometry/WallStrongerLowerReach.lean (Jatloe, N12-jatloe). *)
(* A stronger neighbouring exclusion advances the wall reach to 2.6.         *)
(* short_projections: WFP_SHORT_PROJECTIONS (instantiated by WFP_SP);        *)
(* exists_positive_frame: WCB_EXISTS_POSITIVE_FRAME;                         *)
(* positive_frame_wall_bounds: C977WC_POSITIVE_FRAME_WALL_BOUNDS.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallLowerReach.ml";;

(* Lean: positive_point (private) *)
let WSLR_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     &0 <= c * u - s * (v + a) /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&1) (&91 / &50)) /\
     ~(linside c s u v a (&3 / &2) (&2))
     ==> linside c s u v a (&1) (&13 / &5)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s:real`; SQ_NONNEG `c - s:real`]
    [`&0 <= c * s`; `&1 <= c + s`; `c + s <= &10 / &7`] THEN
  NLIN_FACTS_TAC [] [`&1 + (&41 / &50) * c * s <= c + s`] THEN
  MP_TAC(WFP_SP `&0` `&39 / &50`) THEN
  MP_TAC(WFP_SP `&1 / &2` `&9 / &50`) THEN
  MP_TAC(WFP_SP `--(&1 / &2)` `&3 / &5`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `u + a <= c * &3 / &2 + s * &2 \/ --s * &3 / &2 + c * &2 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &1 + s * &91 / &50 <= u \/ --s * &1 + c * &91 / &50 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
  [SUBGOAL_THEN `--s * &3 / &2 + c * &2 <= v` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   NLIN_FACTS_TAC []
    [`&0 <= s * (v - (--s * &1 + c * &91 / &50))`; `&0 < (a - &1) * (c + s)`;
     `&0 <= c * ((c * &1 + s * &13 / &5) - (u + a))`] THEN
   NLIN_TAC ~deg2:false []]);;

(* Lean: point *)
let WSLR_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&1) (&91 / &50)) /\
     ~(linside c s u v a (&3 / &2) (&2))
     ==> linside c s u v a (&1) (&13 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a (&1) (&13 / &5)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC WSLR_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real`; `y:real`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN REAL_ARITH_TAC);;
