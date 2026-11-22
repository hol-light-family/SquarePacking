(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976MergedLeft/Inputs.lean          *)
(* (N12Compact.Completion.OtherCases.C976MergedLeft).  Literal physical      *)
(* inputs of C976-MERGED-LEFT-ENDING Theorem 1.  The structures Input and    *)
(* Profile are occ976ml_input and occ976ml_profile; square q is c s u v a,   *)
(* square r is cr sr ur vr ar; C976LeftTop.UpperPoints.Input is             *)
(* occ976lt_input.  Tag occ976ml_ / OCC976ML_.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_PointSign.ml";;

(* Lean: Input (structure) *)
let occ976ml_input = new_definition
 `occ976ml_input c s u v a <=>
    &1 < a /\
    linside c s u v a (--(&43 / &500)) (&0) /\
    linside c s u v a (&13 / &20) (&7 / &20) /\
    linside c s u v a (&0) (&13 / &50) /\
    ~linside c s u v a (&1 / &2) (&0) /\
    ~linside c s u v a (&0) (&1) /\
    (forall x. &27 / &100 <= x ==> x <= &37 / &50 ==> ~linside c s u v a x (&1)) /\
    (forall t. &0 <= t ==> t <= &1 ==>
         ~linside c s u v a (--(&6) / &25 + (&6 / &25) * t)
                            (--(&13) / &100 - (&13 / &100) * t))`;;

(* Lean: Input.reframe *)
let OCC976ML_INPUT_REFRAME = prove
 (`forall c s u v a cr sr ur vr ar.
     occ976ml_input c s u v a /\ ar = a /\
     (forall x y. linside cr sr ur vr ar x y <=> linside c s u v a x y)
     ==> occ976ml_input cr sr ur vr ar`,
  REPEAT GEN_TAC THEN REWRITE_TAC[occ976ml_input] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Lean: Input.with_missing_target *)
let OCC976ML_INPUT_WITH_MISSING_TARGET = prove
 (`forall c s u v a.
     occ976ml_input c s u v a /\ ~linside c s u v a (&27 / &100) (--(&1 / &25))
     ==> occ976lt_input c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[occ976ml_input; occ976lt_input] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `&27 / &100`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* Lean: Profile (structure) *)
let occ976ml_profile = new_definition
 `occ976ml_profile (c:real) s u v a <=>
    &0 < c /\ &0 < s /\ s <= c /\ (&38 / &65) * c < s /\
    --(&1 / &2) * s <= v /\ v + a <= c /\ u + a <= (&27 / &100) * c + s`;;
