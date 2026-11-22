(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/MarkerHalfpoint.lean                 *)
(* (namespace N12Compact.C1092MMMPMarkerHalfpoint).                          *)
(* canonical_frame: CLF_CANONICAL_FRAME; short_projections:                  *)
(* WFP_SHORT_PROJECTIONS.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* REAL_ARITH over the assumptions that are real relations or conjunctions *)
let C1092MMH_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* use the missing point (x,y): its four alternatives against the known facts *)
let C1092MMH_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092MMH_LIN_TAC;;

let C1092MMH_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092MMH_MISS_TAC x y; ALL_TAC];;

let C1092MMH_SP dx dy =
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

let C1092MMH_PREP_TAC facts =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  NLIN_FACTS_TAC [] ([`d * c <= &13 / &50 * c`; `&0 <= d * c`] @ facts) THEN
  C1092MMH_SP `&1 / &2` `&37 / &50` THEN
  C1092MMH_SP `&37 / &50` `--(&1 / &2)` THEN
  C1092MMH_SP `&1 / &2` `--(&13 / &50)` THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  REWRITE_TAC[linside];;

(* Lean: positive (private) *)
let C1092MMH_POSITIVE = prove
 (`forall c s u v a d.
     c * c + s * s = &1 /\ &0 < a /\
     &0 <= d /\ d <= &13 / &50 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&1) (--(&13 / &50)) /\
     linside c s u v a (&1) (--(&2 / &5)) /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&1 + d) (&0) /\
     ~linside c s u v a (&1) (--(&1)) /\
     ~linside c s u v a (&13 / &50) (--(&1))
     ==> linside c s u v a (&1) (--(&1 / &2))`,
  C1092MMH_PREP_TAC [`d * s <= &13 / &50 * s`; `&0 <= d * s`] THEN
  C1092MMH_FACT_TAC `--s - c <= v` `&1` `--(&1)` THEN
  C1092MMH_FACT_TAC `u + a <= c * (&1 + d)` `&1 + d` `&0` THEN
  C1092MMH_FACT_TAC `v + a <= --s * &13 / &50` `&13 / &50` `&0` THEN
  C1092MMH_LIN_TAC);;

(* Lean: negative (private) *)
let C1092MMH_NEGATIVE = prove
 (`forall c s u v a t d.
     c * c + s * s = &1 /\ &0 < a /\ s = --t /\
     &0 <= d /\ d <= &13 / &50 /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&1) (--(&13 / &50)) /\
     linside c s u v a (&1) (--(&2 / &5)) /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&1 + d) (&0) /\
     ~linside c s u v a (&1) (--(&1)) /\
     ~linside c s u v a (&13 / &50) (--(&1))
     ==> linside c s u v a (&1) (--(&1 / &2))`,
  C1092MMH_PREP_TAC [`&13 / &50 * s <= d * s`; `d * s <= &0`] THEN
  SUBGOAL_THEN `v < t - c / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MMH_FACT_TAC `c * &13 / &50 <= u` `&13 / &50` `&0` THEN
    C1092MMH_FACT_TAC `u + a <= c * (&1 + d)` `&1 + d` `&0` THEN
    C1092MMH_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c + t / &2 < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MMH_FACT_TAC `v + a <= t * &13 / &50` `&13 / &50` `&0` THEN
    C1092MMH_FACT_TAC `u + a <= c + t` `&1` `--(&1)` THEN
    C1092MMH_FACT_TAC `u + a <= c * &13 / &50 + t` `&13 / &50` `--(&1)` THEN
    C1092MMH_LIN_TAC;
    ALL_TAC] THEN
  C1092MMH_LIN_TAC);;

(* Lean: point *)
let C1092MMH_POINT = prove
 (`forall c s u v a d.
     c * c + s * s = &1 /\ &0 < a /\
     &0 <= d /\ d <= &13 / &50 /\ &1 < a /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&1) (--(&13 / &50)) /\
     linside c s u v a (&1) (--(&2 / &5)) /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&1 + d) (&0) /\
     ~linside c s u v a (&1) (--(&1)) /\
     ~linside c s u v a (&13 / &50) (--(&1))
     ==> linside c s u v a (&1) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a' (&1) (--(&1 / &2))` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `&0 <= s'` THENL
   [MATCH_MP_TAC C1092MMH_POSITIVE THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C1092MMH_NEGATIVE THEN
    MAP_EVERY EXISTS_TAC [`--s':real`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
