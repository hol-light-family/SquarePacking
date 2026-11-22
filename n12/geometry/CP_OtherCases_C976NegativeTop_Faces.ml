(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976NegativeTop/Faces.lean          *)
(* (N12Compact.Completion.OtherCases.C976NegativeTop).  The northeast-square *)
(* premises and forced faces.  Lean's square N with N.s = -s is              *)
(* (c, s, u, v, a) with s = --t.  Alternative / Faces are the predicates     *)
(* cc976f_alternative / cc976f_faces.  mixed_angle: CC976MA_MIXED_ANGLE;     *)
(* OutwardScalars.increasing_projection: CCOS_INCREASING_PROJECTION;         *)
(* S12.short_projections: FSAF_SHORT_PROJECTIONS.                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareAForced.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_MixedAngle.ml";;

(* Lean: Alternative (definition) *)
let cc976f_alternative = new_definition
 `cc976f_alternative c s u v a <=>
    (linside c s u v a (&0) (--(&19 / &50)) /\ ~linside c s u v a (&0) (--(&37 / &50))) \/
    (linside c s u v a (&0) (--(&37 / &50)) /\
     forall x. &13 / &50 <= x /\ x <= &1 / &2 ==> ~linside c s u v a x (--(&1)))`;;

(* Lean: Faces (structure) *)
let cc976f_faces = new_definition
 `cc976f_faces (c:real) (s:real) u v a t <=>
    &0 <= u /\ u < (&13 / &50) * c /\ u < (&37 / &50) * t /\ v < &0 /\
    u + a <= c + (&11 / &25) * t /\ --c <= v /\
    (--(&37 / &50) * c <= v \/ ((&1 / &2) * t - c <= v /\ t < (&13 / &25) * c))`;;

let CC976F_MISSING_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: faces *)
let CC976F_FACES = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &1 < a /\ &0 < c /\ &0 < t /\ t <= c /\
     linside c s u v a (&7 / &20) (--(&13 / &20)) /\
     linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (&1) (--(&11 / &25)) /\
     cc976f_alternative c s u v a
     ==> cc976f_faces c s u v a t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + --t * --t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c (--t) u v a (&7 / &20) (--(&13 / &20))`;
    `linside c (--t) u v a (&13 / &50) (&0)`] THEN
  SUBGOAL_THEN `v < &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
  [CC976F_MISSING_TAC `~linside c (--t) u v a (&0) (&0)`; ALL_TAC] THEN
  let finish =
    SUBGOAL_THEN `u + a <= c + (&11 / &25) * t` ASSUME_TAC THENL
    [CC976F_MISSING_TAC `~linside c (--t) u v a (&1) (--(&11 / &25))`; ALL_TAC] THEN
    REWRITE_TAC[cc976f_faces] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC in
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o REWRITE_RULE[cc976f_alternative] o
    check (fun th -> can (term_match [] `cc976f_alternative c s u v a`) (concl th))) THENL
  [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside] o
     check (fun th -> concl th = `linside c (--t) u v a (&0) (--(&19 / &50))`)) THEN
   SUBGOAL_THEN `--(&37 / &50) * c <= v` ASSUME_TAC THENL
   [CC976F_MISSING_TAC `~linside c (--t) u v a (&0) (--(&37 / &50))`; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `t:real`; `&3 / &10`; `&1`] CCOS_INCREASING_PROJECTION) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
                   DISCH_TAC] THEN
   SUBGOAL_THEN `t - (&11 / &25) * c < v + a` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   finish;
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside] o
     check (fun th -> concl th = `linside c (--t) u v a (&0) (--(&37 / &50))`)) THEN
   MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `t:real`]
     CC976MA_MIXED_ANGLE) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                   STRIP_TAC] THEN
   MP_TAC(SPECL [`c:real`; `--t`; `&1 / &2`; `&14 / &25`] FSAF_SHORT_PROJECTIONS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
   SUBGOAL_THEN `t - (&11 / &25) * c < v + a` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   finish]);;

(* Lean: alternative_anchor *)
let CC976F_ALTERNATIVE_ANCHOR = prove
 (`forall c s u v a. cc976f_alternative c s u v a ==> exists y. y < &0 /\ linside c s u v a (&0) y`,
  REWRITE_TAC[cc976f_alternative] THEN REPEAT STRIP_TAC THENL
  [EXISTS_TAC `--(&19 / &50)`; EXISTS_TAC `--(&37 / &50)`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
