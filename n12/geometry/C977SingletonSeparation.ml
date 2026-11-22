(* ========================================================================= *)
(* Port of Compact/Geometry/C977SingletonSeparation.lean                     *)
(* (N12Compact.C977SingletonSeparation).  A tilted-face restriction from a   *)
(* bottom singleton O and the southwest central square A.                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: bottom_alternatives *)
let C977SS_BOTTOM_ALTERNATIVES = prove
 (`forall cO sO uO vO aO cA sA uA vA aA.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     &0 < cO /\ sO <= &0 /\ --cO <= sO /\
     &0 < cA /\ sA <= &0 /\ --cA <= sA /\
     aO = aA /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     ldisj cO sO uO vO aO cA sA uA vA aA
     ==> vO + aO <= ABT_lower cA sA uA vA aA (--sO) cO \/
         ABT_upper cO sO uO vO aO (--sA) cA <= vA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  let sO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aA:real`]
  and sA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] in
  ABT_ALL_SB_TAC
    [sO,(`&28 / &25`,`&1`); sO,(`&187 / &100`,`&19 / &25`);
     sA,(`&33 / &20`,`&33 / &20`); sA,(`&2`,`&87 / &50`)]
    [`cO:real`,`sO:real`; `--sO`,`cO:real`; `cA:real`,`sA:real`; `--sA`,`cA:real`] THEN
  ABT_OWN_TAC sO THEN ABT_OWN_TAC sA THEN
  ABT_ARITH_TAC);;
