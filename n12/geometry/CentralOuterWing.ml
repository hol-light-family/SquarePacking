(* ========================================================================= *)
(* Port of Compact/Geometry/CentralOuterWing.lean (Jatloe N12).               *)
(* An inward central point forces the adjacent outer wing point (8/5,3).     *)
(* short_projections: WFP_SHORT_PROJECTIONS (via WFP_SP);                    *)
(* exists_positive_frame: WCB_EXISTS_POSITIVE_FRAME.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

let COW_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* Lean: positive_point (private) *)
let COW_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 <= c /\ &0 <= s /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&3 / &2) (&2)
     ==> linside c s u v a (&8 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  MP_TAC(WFP_SP `&17 / &20` `&7 / &20`) THEN
  MP_TAC(WFP_SP `&13 / &20` `&3 / &4`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  REWRITE_TAC[linside] THEN
  COW_ARITH_TAC);;

(* Lean: point *)
let COW_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&3 / &2) (&2)
     ==> linside c s u v a (&8 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a' (&8 / &5) (&3)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC COW_POSITIVE_POINT THEN ASM_REWRITE_TAC[]);;
