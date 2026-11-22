(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C715/FourPointEnding.lean           *)
(* (N12Compact.Completion.OtherCases.C715).  One common four-point           *)
(* obstruction for the first eight C715 ownership alternatives.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: four_point_ending *)
let OCC715FPE_FOUR_POINT_ENDING = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&2) (&113 / &50) /\
      linside c s u v a (&3) (&8 / &5)
      ==> linside c s u v a (&113 / &50) (&2) \/ linside c s u v a (&3) (&113 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&113 / &50 - &3` `&2 - &113 / &50`) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
