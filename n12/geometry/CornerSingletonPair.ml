(* ========================================================================= *)
(* Port of Compact/Geometry/CornerSingletonPair.lean                         *)
(* (N12Compact.CornerSingletonPair).  The two corner singletons O (bottom)   *)
(* and L (left, owning (1,1)) have one directed axis per signed frame.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: Directed *)
let CSP_directed = new_definition
 `CSP_directed cO sO uO vO aO cL sL uL vL aL (c:real) (s:real) <=>
    (&0 <= s /\ ABT_upper cO sO uO vO aO (--s) c <= ABT_lower cL sL uL vL aL (--s) c) \/
    (s < &0 /\ ABT_upper cL sL uL vL aL c s <= ABT_lower cO sO uO vO aO c s)`;;

(* Lean: alternatives *)
let CSP_ALTERNATIVES = prove
 (`forall cO sO uO vO aO cL sL uL vL aL.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cO /\ &0 < cL /\ aO = aL /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cL sL uL vL aL (&1) (&1) /\
     ldisj cO sO uO vO aO cL sL uL vL aL
     ==> CSP_directed cO sO uO vO aO cL sL uL vL aL cO sO \/
         CSP_directed cO sO uO vO aO cL sL uL vL aL cL sL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  REWRITE_TAC[CSP_directed] THEN
  let sO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aL:real`]
  and sL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] in
  ABT_ALL_SB_TAC
    [sO,(`&1`,`&457 / &500`); sO,(`&28 / &25`,`&1`); sO,(`&187 / &100`,`&19 / &25`);
     sL,(`&1`,`&1`)]
    [`cO:real`,`sO:real`; `--sO`,`cO:real`; `cL:real`,`sL:real`; `--sL`,`cL:real`] THEN
  ABT_ARITH_TAC);;

(* Lean: positive_alternatives *)
let CSP_POSITIVE_ALTERNATIVES = prove
 (`forall cO sO uO vO aO cL sL uL vL aL.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cO /\ &0 <= sO /\ &0 < cL /\ &0 <= sL /\ aO = aL /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cL sL uL vL aL (&1) (&1) /\
     ldisj cO sO uO vO aO cL sL uL vL aL
     ==> vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO \/
         ABT_upper cO sO uO vO aO (--sL) cL <= vL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] CSP_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CSP_directed] THEN
  ABT_OWN_TAC [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] THEN
  ABT_OWN_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  ABT_ARITH_TAC);;
