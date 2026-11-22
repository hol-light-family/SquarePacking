(* ========================================================================= *)
(* Phase 2: Compact/Completion/C1092/MPPMInwardFinalRightBar.lean.           *)
(* All-angle wall reach at w = 8/5, d = 87/50, z = 206/85, and the inward    *)
(* right bar.  Squares are 5-tuples c s u v a (p2_base.ml);                 *)
(* R.translated 2 2 is  c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a *)
(* (WSC_INSIDE_TRANSLATED).  S12.left_wall_vertex is MPPMIF_LEFT_WALL_VERTEX. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/C977WallChains.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;
needs "n12/geometry/WallSignChord.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: S12.left_wall_vertex (source/S12/WallBridge.lean) *)
let MPPMIF_LEFT_WALL_VERTEX = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ (forall x y. linside c s u v a x y ==> &0 <= x)
     ==> &0 <= c * u - s * (v + a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977WC_AFFINE_ENDPOINT THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + t) - s * (v + a - t)`; `s * (u + t) + c * (v + a - t)`]) THEN
  ANTS_TAC THENL [MATCH_MP_TAC C977WC_ROT_INSIDE THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: positive_reach (private) *)
let MPPMIF_POSITIVE_REACH = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     &0 <= c * u - s * (v + a) /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&1) (&8 / &5)) /\
     ~(linside c s u v a (&87 / &50) (&2))
     ==> linside c s u v a (&1) (&206 / &85)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s:real`; SQ_NONNEG `c - s:real`]
    [`&0 <= c * s`; `&1 <= c + s`; `c + s <= &10 / &7`] THEN
  NLIN_FACTS_TAC [] [`&1 + (&14 / &17) * c * s <= c + s`] THEN
  MP_TAC(WFP_SP `&0` `&14 / &17`) THEN
  MP_TAC(WFP_SP `&37 / &50` `&2 / &5`) THEN
  MP_TAC(WFP_SP `--(&37 / &50)` `&36 / &85`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `u + a <= c * &87 / &50 + s * &2 \/ --s * &87 / &50 + c * &2 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &1 + s * &8 / &5 <= u \/ --s * &1 + c * &8 / &5 <= v`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= s * (v - (--s * &1 + c * &8 / &5))`; `&0 < (a - &1) * (c + s)`;
      `&0 <= c * ((c * &1 + s * &206 / &85) - (u + a))`] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: left_reach *)
let MPPMIF_LEFT_REACH = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ (forall x y. linside c s u v a x y ==> &0 <= x) /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&1) (&8 / &5)) /\
     ~(linside c s u v a (&87 / &50) (&2))
     ==> linside c s u v a (&1) (&206 / &85)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] WCB_EXISTS_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a (&1) (&206 / &85)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MPPMIF_POSITIVE_REACH THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MPPMIF_LEFT_WALL_VERTEX THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MPPMIF_TI = prove
 (`forall c s u v a x y. linside (--c) (--s) (u - &4 * s - &4 * c) (v - &4 * c + &4 * s) a x y <=>
                   linside c s u v a (&4 - x) (&4 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: right_bar *)
let MPPMIF_RIGHT_BAR = prove
 (`forall c s u v a cN sN uN vN aN.
     c * c + s * s = &1 /\ &1 < a /\ (forall x y. linside c s u v a x y ==> x <= &4) /\
     linside c s u v a (&1543 / &500) (&2) /\ linside c s u v a (&3) (&8 / &5) /\
     linside c s u v a (&3) (&2) /\
     linside cN sN uN vN aN (&3) (&12 / &5) /\ linside cN sN uN vN aN (&113 / &50) (&2) /\
     ldisj c s u v a cN sN uN vN aN
     ==> forall y. --(&36 / &85) <= y /\ y <= &0
             ==> linside c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a (&1) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linside c s u v a (&3) (&134 / &85)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`--c:real`; `--s:real`; `u - &4 * s - &4 * c`; `v - &4 * c + &4 * s`; `a:real`]
             MPPMIF_LEFT_REACH) THEN
    REWRITE_TAC[MPPMIF_TI] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[REAL_ARITH `&4 - x <= &4 ==> &0 <= x`];
      UNDISCH_TAC `ldisj c s u v a cN sN uN vN aN` THEN REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `ldisj c s u v a cN sN uN vN aN` THEN REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WSC_INSIDE_TRANSLATED] THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&134 / &85`; `&2`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
