(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/Main.lean               *)
(* (namespace N12Compact.Completion.OtherCases.C976LeftTop).                *)
(* The complete local Theorem 1 of C976-LEFT-TOP-ANGLE.  N = (cN, sN, uN,    *)
(* vN, aN), W = (cW, sW, uW, vW, aW) with explicit OpenSquare invariants;    *)
(* LeftInput = c976lti_left, TopInput = oltstsu_top, QuadrantData =          *)
(* oltstsu_quadrant, apart = ldisj.  turnFrame W is the tuple                *)
(* (--sW, cW, vW, --uW - aW, aW) (C976LTMN_TURN_INSIDE = S12.turnFrame_inside);*)
(* TopInput.reframe = OLTSTSU_TOP_REFRAME.  Tag C976LTMN_.                    *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C976LeftTop_SmallAngles.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_LargeSupports.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Directions.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_TopFaces.ml";;

(* S12.turnFrame_inside *)
let C976LTMN_TURN_INSIDE = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C976LTMN_VARS = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;

(* Lean: quadrant_impossible *)
let C976LTMN_QUADRANT_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c976lti_left cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     oltstsu_quadrant cW sW /\ aN = aW /\
     ldisj cN sN uN vN aN cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c976lti_left] o
    check (fun th -> concl th = `c976lti_left cN sN uN vN aN`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[oltstsu_top] o
    check (fun th -> concl th = `oltstsu_top cW sW uW vW aW`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[oltstsu_quadrant] o
    check (fun th -> concl th = `oltstsu_quadrant cW sW`)) THEN
  MP_TAC(SPECL C976LTMN_VARS C976LTD_LONGITUDINAL_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  MP_TAC(SPECL C976LTMN_VARS C976LTTF_TOP_LOWERV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `sN <= cN / &3` THENL
   [MP_TAC(SPECL C976LTMN_VARS C976LTSA_SMALL_IMPOSSIBLE) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(&1 / &3) * cN <= sN` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th) &&
      can (find_term ((=) `ABT_upper`)) (concl th))) THENL
     [MP_TAC(SPECL C976LTMN_VARS C976LTLS_LEFT_AXIS_IMPOSSIBLE) THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL C976LTMN_VARS C976LTLS_TOP_AXIS_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]]]);;

(* Lean: nonpositive_impossible *)
let C976LTMN_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c976lti_left cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     &0 < cW /\ sW <= &0 /\ --sW <= (&2 / &3) * cW /\ aN = aW /\
     ldisj cN sN uN vN aN cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `oltstsu_top (--sW) cW vW (--uW - aW) aW` ASSUME_TAC THENL
   [MATCH_MP_TAC OLTSTSU_TOP_REFRAME THEN
    MAP_EVERY EXISTS_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
    ASM_REWRITE_TAC[C976LTMN_TURN_INSIDE]; ALL_TAC] THEN
  SUBGOAL_THEN `ldisj cN sN uN vN aN (--sW) cW vW (--uW - aW) aW` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cN sN uN vN aN cW sW uW vW aW` THEN
    REWRITE_TAC[ldisj; C976LTMN_TURN_INSIDE]; ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `--sW`; `cW:real`; `vW:real`; `--uW - aW`; `aW:real`] C976LTMN_QUADRANT_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[oltstsu_quadrant] THEN RASM_ARITH_TAC);;

(* Lean: steep_negative *)
let C976LTMN_STEEP_NEGATIVE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c976lti_left cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     &0 < cW /\ sW <= &0 /\ aN = aW /\
     ldisj cN sN uN vN aN cW sW uW vW aW
     ==> (&2 / &3) * cW < --sW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL C976LTMN_VARS C976LTMN_NONPOSITIVE_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;
