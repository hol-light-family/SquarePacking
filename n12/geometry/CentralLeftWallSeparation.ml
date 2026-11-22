(* ========================================================================= *)
(* Port of Compact/Geometry/CentralLeftWallSeparation.lean                   *)
(* (N12Compact.CentralLeftWallSeparation).  The left wall square W lies      *)
(* above a central square A owning (1,2) on one of their transverse axes.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

let CLWS_PTS =
  ["A",(`&1`,`&2`); "W",(`&457 / &500`,`&2`); "W",(`&1`,`&113 / &50`)];;

(* Lean: alternatives *)
let CLWS_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cW sW uW vW aW.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &0 < cA /\ &0 <= sA /\ &0 < cW /\ &0 <= sW /\ aA = aW /\
     linside cA sA uA vA aA (&1) (&2) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> vA + aA <= ABT_lower cW sW uW vW aW (--sA) cA \/
         ABT_upper cA sA uA vA aA (--sW) cW <= vW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ABT_PAIR_TAC "A" "W" CLWS_PTS);;

(* Lean: negative_alternatives *)
let CLWS_NEGATIVE_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cW sW uW vW aW.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &0 < cA /\ &0 <= sA /\ &0 < cW /\ sW <= &0 /\ aA = aW /\
     linside cA sA uA vA aA (&1) (&2) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> vA + aA <= ABT_lower cW sW uW vW aW (--sA) cA \/
         uW + aW <= ABT_lower cA sA uA vA aA cW sW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ABT_PAIR_TAC "A" "W" CLWS_PTS);;
