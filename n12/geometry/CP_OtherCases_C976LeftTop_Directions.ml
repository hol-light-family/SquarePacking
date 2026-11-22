(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/Directions.lean         *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.Directions).               *)
(* C976-LEFT-TOP-ANGLE section 1: the actual Z = (1/4,1) and A0 = (11/25,1) *)
(* give the strict separating cone.  Square N is cN sN uN vN aN, square W   *)
(* is cW sW uW vW aW; same proof scheme as OrdinaryLeftTop/ShallowTop-      *)
(* Directions (ABT_FOUR_AXES = CongruentSAT.faceSeparation_of_disjoint with *)
(* the parallel/transverse radii, ABT_ALL_SB_TAC = strict_bounds).          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Inputs.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: forward_cone *)
let C976LTD_FORWARD_CONE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW nx ny.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cN sN uN vN aN (&13 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&1 / &4) (&1) /\
     linside cW sW uW vW aW (&11 / &25) (&1) /\
     ABT_upper cN sN uN vN aN nx ny <= ABT_lower cW sW uW vW aW nx ny
     ==> &0 < nx /\ &21 / &65 * nx < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_ALL_SB_TAC
   [[`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&13 / &20`, `&7 / &20`);
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&1 / &4`, `&1`);
    [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`], (`&11 / &25`, `&1`)]
   [`nx:real`, `ny:real`] THEN
  ABT_ARITH_TAC);;

(* Lean: backward_cone *)
let C976LTD_BACKWARD_CONE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW nx ny.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cN sN uN vN aN (&13 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&1 / &4) (&1) /\
     linside cW sW uW vW aW (&11 / &25) (&1) /\
     ABT_upper cW sW uW vW aW nx ny <= ABT_lower cN sN uN vN aN nx ny
     ==> nx < &0 /\ ny < &21 / &65 * nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_ALL_SB_TAC
   [[`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&13 / &20`, `&7 / &20`);
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&1 / &4`, `&1`);
    [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`], (`&11 / &25`, `&1`)]
   [`nx:real`, `ny:real`] THEN
  ABT_ARITH_TAC);;

(* Lean: longitudinal_alternatives *)
let C976LTD_LONGITUDINAL_ALTERNATIVES = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &0 < cN /\ &0 <= sN /\ &0 <= cW /\ &0 < sW /\
     aN = aW /\
     linside cN sN uN vN aN (&13 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&1 / &4) (&1) /\
     linside cW sW uW vW aW (&11 / &25) (&1) /\
     ldisj cN sN uN vN aN cW sW uW vW aW
     ==> ABT_upper cN sN uN vN aN cN sN <= ABT_lower cW sW uW vW aW cN sN \/
         ABT_upper cN sN uN vN aN cW sW <= ABT_lower cW sW uW vW aW cW sW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABT_ALL_SB_TAC
   [[`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&13 / &20`, `&7 / &20`);
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&1 / &4`, `&1`);
    [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`], (`&11 / &25`, `&1`)]
   [`cN:real`, `sN:real`; `--sN:real`, `cN:real`; `cW:real`, `sW:real`; `--sW:real`, `cW:real`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  ABT_ARITH_TAC);;

