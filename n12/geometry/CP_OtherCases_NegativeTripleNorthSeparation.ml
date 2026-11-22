(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/NegativeTripleNorthSeparation.lean  *)
(* (N12Compact.Completion.OtherCases.NegativeTripleNorthSeparation).  The    *)
(* northeast/right separating-axis reduction.  Squares N, R are             *)
(* cN sN uN vN aN, cR sR uR vR aR (unit normals and positive sides explicit).*)
(* upper / lower: ABT_upper / ABT_lower; strict_bounds: ABT_STRICT_BOUNDS;   *)
(* RightTripleData.RightProfile: ocrtd_rightprofile; TopOnlyQuadrantProfile. *)
(* Data: octoqp_data; TopOnlyQuadrantScalars.profile_bounds:                 *)
(* OCTOQS_PROFILE_BOUNDS; C981CompletionSupportForms.upper_in_bands:         *)
(* C981SF_UPPER_IN_BANDS; WallProfile.upper_neg / lower_neg: OCWPVG_*_NEG;   *)
(* faceSeparation_of_disjoint + separated + parallel/transverse_radius:      *)
(* ABT_FOUR_AXES.  Tag OCNTNS_.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_RightTripleData.ml";;
needs "n12/geometry/CP_OtherCases_SupportBands.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;

let OCNTNS_LIN = NLIN_TAC ~deg2:false [];;

let OCNTNS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN CONJ_TAC THEN
   OCNTNS_LIN; ALL_TAC];;

(* Lean: upper_pp (private) *)
let OCNTNS_UPPER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_upper c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC);;

(* Lean: cone *)
let OCNTNS_CONE = prove
 (`forall cN sN uN vN aN cR sR uR vR aR nx ny.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
     linside cN sN uN vN aN (&1 / &2) (&1) /\
     ocrtd_rightprofile cR sR uR vR aR /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cN sN uN vN aN nx ny <= ABT_lower cR sR uR vR aR nx ny
     ==> &0 < nx /\ ny < (&1 / &2) * nx /\ &0 < (&19 / &40) * nx + (&87 / &200) * ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocrtd_rightprofile] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `&1 / &2`; `&1`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `&21 / &40`; `&1 / &8`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `&1`; `&0`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `&1`; `&14 / &25`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN OCNTNS_LIN);;

(* Lean: no_right_v (private) *)
let OCNTNS_NO_RIGHT_V = prove
 (`forall cN sN uN vN aN cR sR uR vR aR.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aN /\ octoqp_data cN sN uN vN aN /\ ocrtd_rightprofile cR sR uR vR aR /\
     linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
     linside cN sN uN vN aN (&1 / &2) (&1) /\
     ABT_upper cN sN uN vN aN (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `--sR`; `cR:real`]
    OCNTNS_CONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cR * cR + sR * sR = &1` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] OCTOQS_PROFILE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[octoqp_data] o
    check (fun th -> concl th = `octoqp_data cN sN uN vN aN`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ocrtd_rightprofile] o
    check (fun th -> concl th = `ocrtd_rightprofile cR sR uR vR aR`)) THEN
  (* alphaPositive, deltaPositive *)
  OCNTNS_PROD `&0 < --sR * (cN - &1 / &2 * --sN)` THEN
  OCNTNS_PROD `&0 <= --sN * (&1 / &2 * --sR - cR)` THEN
  SUBGOAL_THEN `&0 < cN * --sR - --sN * cR` ASSUME_TAC THENL [OCNTNS_LIN; ALL_TAC] THEN
  OCNTNS_PROD `&0 < --sN * --sR` THEN
  OCNTNS_PROD `&0 < cN * cR` THEN
  SUBGOAL_THEN `&0 < --sN * --sR + cN * cR` ASSUME_TAC THENL [OCNTNS_LIN; ALL_TAC] THEN
  (* formula *)
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `--sR`; `cR:real`]
    OCNTNS_UPPER_PP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN OCNTNS_LIN; DISCH_TAC] THEN
  (* highU, highV products *)
  OCNTNS_PROD `&0 < (cN * --sR - --sN * cR) * ((uN + aN) - (&1 - --sN))` THEN
  OCNTNS_PROD `&0 < (--sN * --sR + cN * cR) * ((vN + aN) - (&1 + &13 / &50 * cN))` THEN
  SUBGOAL_THEN
   `(cN * --sR - --sN * cR) * (&1 - --sN) + (--sN * --sR + cN * cR) * (&1 + &13 / &50 * cN) =
    --sR * (cN - sN + &37 / &50 * cN * sN) + cR * (cN + sN + &13 / &50 + &37 / &50 * sN * sN)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `cN * cN + sN * sN = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  (* aMargin, bMargin *)
  OCNTNS_PROD `&0 < --sR * ((cN - sN + &37 / &50 * cN * sN) - &1)` THEN
  OCNTNS_PROD `&0 < cR * (cN + sN + &13 / &50 + &37 / &50 * sN * sN)` THEN
  (* origin *)
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `&1`; `&0`;
                `--sR`; `cR:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cR * cR + sR * sR = &1` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  OCNTNS_LIN);;

(* Lean: separators *)
let OCNTNS_SEPARATORS = prove
 (`forall cN sN uN vN aN cR sR uR vR aR.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aN /\ aN = aR /\
     octoqp_data cN sN uN vN aN /\ ocrtd_rightprofile cR sR uR vR aR /\
     linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
     linside cN sN uN vN aN (&1 / &2) (&1) /\
     ldisj cN sN uN vN aN cR sR uR vR aR
     ==> ABT_upper cN sN uN vN aN cN sN <= ABT_lower cR sR uR vR aR cN sN \/
         ABT_upper cN sN uN vN aN cR sR <= ABT_lower cR sR uR vR aR cR sR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] OCTOQS_PROFILE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[octoqp_data] o
    check (fun th -> concl th = `octoqp_data cN sN uN vN aN`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ocrtd_rightprofile] o
    check (fun th -> concl th = `ocrtd_rightprofile cR sR uR vR aR`)) THEN
  let use nx ny =
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; nx; ny] OCNTNS_CONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN
      REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
      STRIP_TAC THEN OCNTNS_LIN] in
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_FOUR_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                       `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] OCNTNS_NO_RIGHT_V) THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         use `--cN` `--sN`;
         use `--sN` `cN:real`;
         use `-- --sN` `--cN`;
         use `--cR` `--sR`;
         use `-- --sR` `--cR`]);;

(* Lean: right_axis_bounds *)
let OCNTNS_RIGHT_AXIS_BOUNDS = prove
 (`forall cN sN uN vN aN cR sR uR vR aR.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_rightprofile cR sR uR vR aR /\
     linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
     linside cN sN uN vN aN (&1 / &2) (&1) /\
     ABT_upper cN sN uN vN aN cR sR <= ABT_lower cR sR uR vR aR cR sR
     ==> &87 * --sR < &95 * cR /\ &2 / &3 < cR /\ --sR < &3 / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `cR:real`; `sR:real`]
    OCNTNS_CONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cR * cR + sR * sR = &1` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ocrtd_rightprofile] o
    check (fun th -> concl th = `ocrtd_rightprofile cR sR uR vR aR`)) THEN
  SUBGOAL_THEN `&87 * --sR < &95 * cR` ASSUME_TAC THENL [OCNTNS_LIN; ALL_TAC] THEN
  OCNTNS_PROD `&0 <= (&95 * cR - &87 * --sR) * (&95 * cR + &87 * --sR)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
   [OCNTNS_PROD `&0 <= (&2 / &3 - cR) * (&2 / &3 + cR)` THEN OCNTNS_LIN;
    OCNTNS_PROD `&0 <= (--sR - &3 / &4) * (--sR + &3 / &4)` THEN OCNTNS_LIN]);;
