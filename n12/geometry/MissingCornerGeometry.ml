(* ========================================================================= *)
(* Port of Completion/Cases/C977/MissingCornerGeometry.lean                  *)
(* (S12Completion.C977).  Strict singleton anchors and a missing corner     *)
(* force the two extended points (91/50,1) and (49/25,19/25).               *)
(* S12.wallCubic is ported locally (c977mcg_wallCubic); the normal bound     *)
(* normal_bound_096 is proved by a Bernstein certificate (ARC_NONNEG)        *)
(* instead of S12.normal_bound_from_cubic.  S12.exists_positive_frame is     *)
(* WCB_EXISTS_POSITIVE_FRAME, positive_frame_wall_bounds is                  *)
(* C977WC_POSITIVE_FRAME_WALL_BOUNDS, normal_bound_small is NB_SMALL.       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "shared/tools/bernstein.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;
needs "n12/geometry/C977WallChains.ml";;

(* Lean: SingletonAnchors (structure) *)
let c977mcg_anchors = new_definition
 `c977mcg_anchors (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    linside c s u v a (&28 / &25) (&1) /\
    linside c s u v a (&87 / &50) (&1) /\
    linside c s u v a (&187 / &100) (&19 / &25)`;;

(* Lean: S12.wallCubic (definition, source/S12/WallCubicData.lean) *)
let c977mcg_wallCubic = new_definition
 `c977mcg_wallCubic (w:real) (delta:real) (t:real) =
    (&1 - w) + (&2 * delta - &1) * t + (&1 + w) * t pow 2 - t pow 3`;;

let C977MCG_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; NLIN_TAC ~deg2:false []]; ALL_TAC];;

(* Lean: wall096_nonnegative *)
let C977MCG_WALL096_NONNEGATIVE = prove
 (`forall t. &0 <= t /\ t <= &1 ==> &0 <= c977mcg_wallCubic (&24 / &25) (&6 / &25) t`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c977mcg_wallCubic] THEN
  ASM_CASES_TAC `t <= &1 / &4` THENL
  [C977MCG_PROD `&0 <= t pow 2 * (&1 / &4 - t)` THEN
   NLIN_TAC ~deg2:false [SQ_NONNEG `&171 * t - &26`];
   ALL_TAC] THEN
  ASM_CASES_TAC `t <= &1 / &2` THENL
  [C977MCG_PROD `&0 <= t pow 2 * (&1 / &2 - t)` THEN
   NLIN_TAC ~deg2:false [SQ_NONNEG `t - &1 / &4`];
   C977MCG_PROD `&0 <= t pow 2 * (&1 - t)` THEN
   NLIN_TAC ~deg2:false [SQ_NONNEG `t - &1 / &2`]]);;

let C977MCG_NB096 =
  ARC_NONNEG `c + s - (c * c + (&19 / &25) * s * s + (&24 / &25) * c * s)`;;

(* Lean: normal_bound_096 *)
let C977MCG_NORMAL_BOUND_096 = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
     ==> c pow 2 + (&19 / &25) * s pow 2 + (&24 / &25) * c * s <= c + s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977MCG_NB096) THEN REAL_ARITH_TAC);;

(* Lean: MissingCornerPoints (structure) *)
let c977mcg_points = new_definition
 `c977mcg_points (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    linside c s u v a (&91 / &50) (&1) /\
    linside c s u v a (&49 / &25) (&19 / &25)`;;

(* the argument in the positive frame (body of the Lean proof) *)
let C977MCG_FRAME = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y) /\
     linside c s u v a (&1) (&457 / &500) /\
     linside c s u v a (&28 / &25) (&1) /\
     linside c s u v a (&87 / &50) (&1) /\
     linside c s u v a (&187 / &100) (&19 / &25) /\
     ~linside c s u v a (&1) (&1)
     ==> linside c s u v a (&91 / &50) (&1) /\
         linside c s u v a (&49 / &25) (&19 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= s * u + c * v` ASSUME_TAC THENL
  [UNDISCH_TAC `a * (c + s) / &2 <= lcy c s u v a` THEN REWRITE_TAC[lcy] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&41 / &50`; `&1`; `&1`; `c:real`; `s:real`] NB_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977MCG_NORMAL_BOUND_096) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC] THEN
  UNDISCH_TAC `~linside c s u v a (&1) (&1)` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `linside c s u v a x y`) (concl th)))) THEN
  REWRITE_TAC[linside] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `v + a <= --s * &1 + c * &1` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C977MCG_PROD `&0 < (a - &1) * (c + s)` THEN
  C977MCG_PROD `&0 <= c * ((--s * &1 + c * &1) - (v + a))` THEN
  SUBGOAL_THEN `&0 < s * (u + a - (c * (&91 / &50) + s * &1))` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * (u + a - (c * (&49 / &25) + s * (&19 / &25)))` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `c * (&91 / &50) + s * &1 < u + a` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C977MCG_PROD `&0 <= s * ((c * (&91 / &50) + s * &1) - (u + a))` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `c * (&49 / &25) + s * (&19 / &25) < u + a` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C977MCG_PROD `&0 <= s * ((c * (&49 / &25) + s * (&19 / &25)) - (u + a))` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `(&24 / &25) * s + (&6 / &25) * c < &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `(&6 / &25) * s - (&24 / &25) * c`]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: missing_corner_points_of_anchors *)
let C977MCG_MISSING_CORNER_POINTS_OF_ANCHORS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&1) (&457 / &500) /\ c977mcg_anchors c s u v a /\
     ~linside c s u v a (&1) (&1)
     ==> c977mcg_points c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977mcg_anchors; c977mcg_points; lcont] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN `u':real`
    (X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `a':real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC C977MCG_FRAME THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
