(* ========================================================================= *)
(* Port of Compact/Geometry/C981Midpoint.lean (Jatloe N12).                   *)
(* Symbolic replacement for C981 InitialV116's angle roots: a forced         *)
(* midpoint (27/10,27/10).  short_projections: WFP_SHORT_PROJECTIONS;        *)
(* exists_positive_frame: WCB_EXISTS_POSITIVE_FRAME; pullSwap: LINSIDE_PULLSW.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

let C981MP_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* Lean: shallow *)
let C981MP_SHALLOW = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 <= c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&113 / &50) (&3) /\
     linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&2) (&113 / &50)
     ==> linside c s u v a (&27 / &10) (&27 / &10)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&7 / &10`; `&11 / &25`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  SUBGOAL_THEN `c * &2 + s * &113 / &50 <= u` ASSUME_TAC THENL
   [C981MP_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN C981MP_ARITH_TAC);;

(* Lean: forced_midpoint *)
let C981MP_FORCED_MIDPOINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&113 / &50) (&3) /\
     linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&2) (&113 / &50) /\
     ~linside c s u v a (&113 / &50) (&2)
     ==> linside c s u v a (&27 / &10) (&27 / &10)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a' (&27 / &10) (&27 / &10)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `s' <= c'` THENL
   [MATCH_MP_TAC C981MP_SHALLOW THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[GSYM LINSIDE_PULLSW] THEN
    MATCH_MP_TAC C981MP_SHALLOW THEN ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN
    ASM_REAL_ARITH_TAC]);;

(* Lean: foreign_midpoint *)
let C981MP_FOREIGN_MIDPOINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     linside c s u v a (&12 / &5) (&3) /\
     linside c s u v a (&3) (&12 / &5)
     ==> linside c s u v a (&27 / &10) (&27 / &10)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: excludes *)
let C981MP_EXCLUDES = prove
 (`forall cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     &1 < aq /\
     linside cq sq uq vq aq (&113 / &50) (&3) /\
     linside cq sq uq vq aq (&3) (&113 / &50) /\
     ~linside cq sq uq vq aq (&2) (&113 / &50) /\
     ~linside cq sq uq vq aq (&113 / &50) (&2) /\
     linside cr sr ur vr ar (&12 / &5) (&3) /\
     linside cr sr ur vr ar (&3) (&12 / &5) /\
     ldisj cq sq uq vq aq cr sr ur vr ar
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `ldisj cq sq uq vq aq cr sr ur vr ar` THEN
  REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`&27 / &10`; `&27 / &10`]) THEN
  REWRITE_TAC[TAUT `~p ==> false <=> p`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C981MP_FORCED_MIDPOINT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C981MP_FOREIGN_MIDPOINT THEN ASM_REWRITE_TAC[]]);;
