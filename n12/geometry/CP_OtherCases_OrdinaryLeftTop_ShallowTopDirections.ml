(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/                    *)
(*   ShallowTopDirections.lean                                               *)
(* (N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopDirections).  *)
(* The initial separating-normal reduction in Theorem 2 of                   *)
(* ORDINARY-LEFT-TOP-OBSTRUCTION.md.  Square N is cN sN uN vN aN, square W  *)
(* is cW sW uW vW aW.  Tag OLTSTD_.                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: forward_cone *)
let OLTSTD_FORWARD_CONE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW nx ny.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cN sN uN vN aN (&13 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&7 / &25) (&1) /\
     linside cW sW uW vW aW (&11 / &25) (&1) /\
     ABT_upper cN sN uN vN aN nx ny <= ABT_lower cW sW uW vW aW nx ny
     ==> &0 < nx /\ &21 / &65 * nx < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_ALL_SB_TAC
   [[`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&13 / &20`, `&7 / &20`);
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&7 / &25`, `&1`);
    [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`], (`&11 / &25`, `&1`)]
   [`nx:real`, `ny:real`] THEN
  ABT_ARITH_TAC);;

(* Lean: backward_cone *)
let OLTSTD_BACKWARD_CONE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW nx ny.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cN sN uN vN aN (&13 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&7 / &25) (&1) /\
     linside cW sW uW vW aW (&11 / &25) (&1) /\
     ABT_upper cW sW uW vW aW nx ny <= ABT_lower cN sN uN vN aN nx ny
     ==> nx < &0 /\ ny < &21 / &65 * nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_ALL_SB_TAC
   [[`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&13 / &20`, `&7 / &20`);
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&7 / &25`, `&1`);
    [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`], (`&11 / &25`, `&1`)]
   [`nx:real`, `ny:real`] THEN
  ABT_ARITH_TAC);;

(* Lean: longitudinal_alternatives *)
let OLTSTD_LONGITUDINAL_ALTERNATIVES = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &0 < cN /\ &0 <= sN /\ &0 <= cW /\ &0 < sW /\
     aN = aW /\
     linside cN sN uN vN aN (&13 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&7 / &25) (&1) /\
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
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`], (`&7 / &25`, `&1`);
    [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`], (`&11 / &25`, `&1`)]
   [`cN:real`, `sN:real`; `--sN:real`, `cN:real`; `cW:real`, `sW:real`; `--sW:real`, `cW:real`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  ABT_ARITH_TAC);;

(* Lean: relative_coefficients *)
let OLTSTD_RELATIVE_COEFFICIENTS = prove
 (`forall l h C S. &0 < l /\ &0 < h /\ h <= l /\ &0 <= C /\ &0 < S /\ C <= &2 / &3 * S
     ==> &0 < l * C + h * S /\ &0 < l * S - h * C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= l * C /\ &0 < h * S /\ &0 < l * (S - C) /\ &0 <= C * (l - h)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;
