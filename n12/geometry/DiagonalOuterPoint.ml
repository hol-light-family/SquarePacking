(* ========================================================================= *)
(* Port of Compact/Geometry/DiagonalOuterPoint.lean (Jatloe N12).             *)
(* The two diagonal boundary points cannot both avoid their outer points.    *)
(* positive_frame: CLF_POSITIVE_FRAME; pullSwap: LINSIDE_PULLSW.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let DOP_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* Lean: shallow (private) *)
let DOP_SHALLOW = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&113 / &50) (&3) /\
     linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&2) (&113 / &50) /\
     ~linside c s u v a (&3) (&12 / &5)
     ==> linside c s u v a (&12 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a <= c + (&7 / &50) * s` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
    DOP_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 * s < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= s * (&3 * s - c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
     [`(c + (&7 / &50) * s) * (c + (&7 / &50) * s) <= &1`] THEN
    NLIN_TAC []; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  REWRITE_TAC[linside] THEN DOP_ARITH_TAC);;

(* Lean: point *)
let DOP_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&113 / &50) (&3) /\
     linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&2) (&113 / &50) /\
     ~linside c s u v a (&113 / &50) (&2)
     ==> linside c s u v a (&12 / &5) (&3) \/ linside c s u v a (&3) (&12 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a' (&12 / &5) (&3) \/
                linside c' s' u' v' a' (&3) (&12 / &5)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `linside c' s' u' v' a (&113 / &50) (&3) /\
    linside c' s' u' v' a (&3) (&113 / &50) /\
    ~linside c' s' u' v' a (&2) (&113 / &50) /\
    ~linside c' s' u' v' a (&113 / &50) (&2)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
  ASM_CASES_TAC `s' <= c'` THENL
   [ASM_CASES_TAC `linside c' s' u' v' a (&3) (&12 / &5)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DOP_SHALLOW THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `linside c' s' u' v' a (&12 / &5) (&3)` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM LINSIDE_PULLSW] THEN
    MATCH_MP_TAC DOP_SHALLOW THEN ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN
    ASM_REAL_ARITH_TAC]);;

(* Lean: impossible *)
let DOP_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&113 / &50) (&3) /\
     linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&2) (&113 / &50) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&12 / &5) (&3) /\
     ~linside c s u v a (&3) (&12 / &5)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] DOP_POINT) THEN
  ASM_REWRITE_TAC[]);;
