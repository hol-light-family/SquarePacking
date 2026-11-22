(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972SoutheastSeparation.lean       *)
(* (namespace N12Compact.FiniteCases.C972Local).  Actual southwest square A  *)
(* versus a positive southeast square E: the west and south crosspoints      *)
(* remove both southeast transverse axes.  lower / upper are ABT_lower /     *)
(* ABT_upper; the four SAT axes come from ABT_FOUR_AXES.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: positive_southeast_alternatives *)
let FC972SS_POSITIVE_SOUTHEAST_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cE sE uE vE aE.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &0 < cA /\ abs sA <= cA /\ &0 < cE /\ &0 <= sE /\ sE <= cE /\ aA = aE /\
     linside cA sA uA vA aA (-- &1 / &2) (&0) /\
     linside cA sA uA vA aA (&0) (-- &1 / &2) /\
     linside cA sA uA vA aA (&0) (-- &13 / &50) /\
     linside cE sE uE vE aE (&7 / &20) (-- &7 / &20) /\
     linside cE sE uE vE aE (&1) (-- &13 / &50) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     ldisj cA sA uA vA aA cE sE uE vE aE
     ==> uA + aA <= ABT_lower cE sE uE vE aE cA sA \/
         ABT_upper cA sA uA vA aA cE sE <= uE \/
         (&17 * sA < -- &7 * cA /\ vA + aA <= ABT_lower cE sE uE vE aE (--sA) cA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_PAIR_TAC "A" "E"
   ["A",(`-- &1 / &2`,`&0`); "A",(`&0`,`-- &1 / &2`); "A",(`&0`,`-- &13 / &50`);
    "E",(`&7 / &20`,`-- &7 / &20`); "E",(`&1`,`-- &13 / &50`); "E",(`&13 / &50`,`&0`)]);;

(* Lean: nonnegative_pair_alternatives *)
let FC972SS_NONNEGATIVE_PAIR_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cE sE uE vE aE.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &0 < cA /\ &0 <= sA /\ abs sA <= cA /\ &0 < cE /\ &0 <= sE /\ sE <= cE /\ aA = aE /\
     linside cA sA uA vA aA (-- &1 / &2) (&0) /\
     linside cA sA uA vA aA (&0) (-- &1 / &2) /\
     linside cA sA uA vA aA (&0) (-- &13 / &50) /\
     linside cE sE uE vE aE (&7 / &20) (-- &7 / &20) /\
     linside cE sE uE vE aE (&1) (-- &13 / &50) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     ldisj cA sA uA vA aA cE sE uE vE aE
     ==> uA + aA <= ABT_lower cE sE uE vE aE cA sA \/
         ABT_upper cA sA uA vA aA cE sE <= uE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    FC972SS_POSITIVE_SOUTHEAST_ALTERNATIVES) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~r ==> (p \/ q \/ (r /\ t) ==> p \/ q)`) THEN
  ASM_REAL_ARITH_TAC);;
