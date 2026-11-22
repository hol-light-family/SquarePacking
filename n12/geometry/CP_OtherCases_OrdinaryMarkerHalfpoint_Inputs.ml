(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryMarkerHalfpoint/Inputs.lean *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint).     *)
(* Literal parameterized hypotheses of ORDINARY-MARKER-HALFPOINT.  The      *)
(* structure Input is the predicate ocomhi_input; square q is c s u v a,    *)
(* square r is cr sr ur vr ar.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: Input (structure) *)
let ocomhi_input = new_definition
 `ocomhi_input c s u v a d <=>
    &1 < a /\ &0 <= d /\ d <= &13 / &50 /\
    linside c s u v a (&7 / &20) (--(&7 / &20)) /\
    linside c s u v a (&1) (--(&13 / &50)) /\
    linside c s u v a (&1) (--(&2 / &5)) /\
    ~linside c s u v a (&13 / &50) (&0) /\
    ~linside c s u v a (&1 + d) (&0) /\
    ~linside c s u v a (&1) (--(&1)) /\
    ~linside c s u v a (&13 / &50) (--(&1))`;;

(* Lean: Input.reframe *)
let OCOMHI_INPUT_REFRAME = prove
 (`forall c s u v a cr sr ur vr ar d.
     ocomhi_input c s u v a d /\ ar = a /\
     (forall x y. linside cr sr ur vr ar x y <=> linside c s u v a x y)
     ==> ocomhi_input cr sr ur vr ar d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocomhi_input] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;
