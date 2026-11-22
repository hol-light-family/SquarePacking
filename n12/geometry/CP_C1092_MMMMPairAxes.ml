(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMPairAxes.lean                        *)
(* (N12Compact.C1092MMMMPairAxes).  The three exhaustive support orders      *)
(* shared by both MMMM pair arguments.                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: alternatives *)
let C1092MPA_ALTERNATIVES = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\ &0 < cC /\ sC <= cC /\ &0 < cB /\ sB <= cB /\
     cC - sC <= &10 / &7 /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     uC + aC <= (&7 / &20) * (cC - sC) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> uB + aB <= ABT_lower cC sC uC vC aC cB sB \/
         vC + aC <= ABT_lower cB sB uB vB aB (--sC) cC \/
         ABT_upper cC sC uC vC aC (--sB) cB <= vB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_PAIR_TAC "C" "B"
    ["C",(`&0`,`&0`); "C",(`--(&7 / &20)`,`--(&7 / &20)`);
     "B",(`--(&7 / &20)`,`&7 / &20`); "B",(`--(&1)`,`&2 / &5`)]);;
