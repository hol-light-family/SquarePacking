(* ========================================================================= *)
(* Port of Compact/Geometry/C977CenterPairSeparation.lean                    *)
(* (N12Compact.C977CenterPairSeparation).  Adjacent central squares can     *)
(* separate only eastward / northward on a longitudinal axis.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: right_alternatives *)
let C977CPS_RIGHT_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &0 < cA /\ abs sA <= cA /\ &0 < cB /\ abs sB <= cB /\ aA = aB /\
     linside cA sA uA vA aA (&2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> uA + aA <= ABT_lower cB sB uB vB aB cA sA \/
         ABT_upper cA sA uA vA aA cB sB <= uB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_PAIR_TAC "A" "B"
    ["A",(`&2`,`&2`); "A",(`&2`,`&3 / &2`); "A",(`&2`,`&87 / &50`);
     "B",(`&47 / &20`,`&33 / &20`); "B",(`&3`,`&87 / &50`); "B",(`&113 / &50`,`&2`)]);;

(* Lean: top_alternatives *)
let C977CPS_TOP_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cC sC uC vC aC.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cC * cC + sC * sC = &1 /\ &0 < aC /\
     &0 < cA /\ abs sA <= cA /\ &0 < cC /\ abs sC <= cC /\ aA = aC /\
     linside cA sA uA vA aA (&2) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cC sC uC vC aC (&33 / &20) (&47 / &20) /\
     linside cC sC uC vC aC (&87 / &50) (&3) /\
     linside cC sC uC vC aC (&2) (&113 / &50) /\
     ldisj cA sA uA vA aA cC sC uC vC aC
     ==> vA + aA <= ABT_lower cC sC uC vC aC (--sA) cA \/
         ABT_upper cA sA uA vA aA (--sC) cC <= vC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_PAIR_TAC "A" "C"
    ["A",(`&2`,`&2`); "A",(`&3 / &2`,`&2`); "A",(`&87 / &50`,`&2`);
     "C",(`&33 / &20`,`&47 / &20`); "C",(`&87 / &50`,`&3`); "C",(`&2`,`&113 / &50`)]);;
