(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/PointInputs.lean        *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints).  Literal      *)
(* inputs of C976-LEFT-UPPER-POINTS.  The structures Input and Profile are  *)
(* the predicates occ976lt_input and occ976lt_profile; square q is          *)
(* c s u v a, square r is cr sr ur vr ar.  Tag occ976lt_ / OCC976LT_.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: Input (structure) *)
let occ976lt_input = new_definition
 `occ976lt_input c s u v a <=>
    &1 < a /\
    linside c s u v a (--(&43 / &500)) (&0) /\
    linside c s u v a (&13 / &20) (&7 / &20) /\
    linside c s u v a (&0) (&13 / &50) /\
    ~linside c s u v a (&1 / &2) (&0) /\
    ~linside c s u v a (&0) (&1) /\
    ~linside c s u v a (&27 / &100) (--(&1 / &25)) /\
    (forall x. &11 / &25 <= x ==> x <= &37 / &50 ==> ~linside c s u v a x (&1)) /\
    (forall t. &0 <= t ==> t <= &1 ==>
         ~linside c s u v a (--(&6) / &25 + (&6 / &25) * t)
                            (--(&13) / &100 - (&13 / &100) * t))`;;

(* Lean: Input.reframe *)
let OCC976LT_INPUT_REFRAME = prove
 (`forall c s u v a cr sr ur vr ar.
     occ976lt_input c s u v a /\ ar = a /\
     (forall x y. linside cr sr ur vr ar x y <=> linside c s u v a x y)
     ==> occ976lt_input cr sr ur vr ar`,
  REPEAT GEN_TAC THEN REWRITE_TAC[occ976lt_input] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Lean: Profile (structure) *)
let occ976lt_profile = new_definition
 `occ976lt_profile (c:real) s u v a <=>
    &0 < c /\ &0 < s /\ s <= c /\
    (&21 / &65) * c < s /\ s < (&3 / &4) * c /\
    --(&27 / &100) * s - (&1 / &25) * c <= v /\
    v + a <= c /\
    u + a <= (&11 / &25) * c + s`;;
