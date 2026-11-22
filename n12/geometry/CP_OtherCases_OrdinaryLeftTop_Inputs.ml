(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/Inputs.lean         *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop).             *)
(* Literal hypotheses of ORDINARY-LEFT-TOP-OBSTRUCTION.md, Theorem 1.  The  *)
(* structure Input is the predicate ocolti_input; square q is c s u v a,    *)
(* square r is cr sr ur vr ar.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: Input (structure) *)
let ocolti_input = new_definition
 `ocolti_input c s u v a <=>
    &1 < a /\
    linside c s u v a (&13 / &20) (&7 / &20) /\
    linside c s u v a (&0) (&13 / &50) /\
    ~linside c s u v a (--(&43 / &500)) (&0) /\
    ~linside c s u v a (&1 / &2) (&0) /\
    ~linside c s u v a (&37 / &50) (&0) /\
    ~linside c s u v a (&0) (&1) /\
    ~linside c s u v a (&27 / &100) (--(&1 / &25)) /\
    ~linside c s u v a (&11 / &25) (&1) /\
    ~linside c s u v a (&37 / &50) (&1)`;;

(* Lean: Input.reframe *)
let OCOLTI_INPUT_REFRAME = prove
 (`forall c s u v a cr sr ur vr ar.
     ocolti_input c s u v a /\ ar = a /\
     (forall x y. linside cr sr ur vr ar x y <=> linside c s u v a x y)
     ==> ocolti_input cr sr ur vr ar`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocolti_input] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;
