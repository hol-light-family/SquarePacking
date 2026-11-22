(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/NegativeTripleFaces.lean            *)
(* (N12Compact.Completion.OtherCases.NegativeTripleFaces).  The negative     *)
(* southeast entrance from its actual marker and elbow.  The structure Data  *)
(* is the predicate ccntf_data; E.s = -t is s = --t.                         *)
(* CanonicalScalars.bounds: CCCS_BOUNDS; BottomBarSupport.negative:          *)
(* CCBBS_NEGATIVE.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_OtherCases_BottomBarSupport.ml";;

(* Lean: Data (structure) *)
let ccntf_data = new_definition
 `ccntf_data c s u v a t <=>
    s = --t /\ &0 < c /\ &0 < t /\ t <= c /\ &1 < a /\ &0 <= u /\ &1 < u + a /\
    u < (&13 / &50) * c /\ v < &0 /\ v + a <= t /\
    v + a <= (&21 / &40) * t + (&1 / &8) * c /\
    (&13 / &50) * t - c <= v /\
    ((&4 / &5) * t - c <= v \/ --(&1) <= --t * (u + a) + c * v)`;;

let CCNTF_MISSING_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: faces *)
let CCNTF_FACES = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &1 < a /\ &0 < c /\ &0 < t /\ t <= c /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (&1) (&0) /\
     ~linside c s u v a (&21 / &40) (&1 / &8) /\
     (forall x. &13 / &50 <= x /\ x <= &4 / &5 ==> ~linside c s u v a x (--(&1)))
     ==> ccntf_data c s u v a t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2] THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `c * c + --t * --t = &1` THEN CONV_TAC REAL_RING; STRIP_TAC] THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c (--t) u v a (&7 / &20) (--(&7 / &20))`;
    `linside c (--t) u v a (&13 / &50) (&0)`] THEN
  SUBGOAL_THEN `v < &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
  [CCNTF_MISSING_TAC `~linside c (--t) u v a (&0) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= t` ASSUME_TAC THENL
  [CCNTF_MISSING_TAC `~linside c (--t) u v a (&1) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&21 / &40) * t + (&1 / &8) * c` ASSUME_TAC THENL
  [CCNTF_MISSING_TAC `~linside c (--t) u v a (&21 / &40) (&1 / &8)`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `t:real`] CCBBS_NEGATIVE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)] THEN
  REWRITE_TAC[ccntf_data] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;
