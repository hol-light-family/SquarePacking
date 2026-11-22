(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974LowerFace.lean             *)
(* (N12Compact.Completion.OtherCases.C983.C974LowerFace).  The actual K-W    *)
(* lower-face argument, section 2 of C974-THREE-SQUARE-ENDING.  Square K is  *)
(* cK sK uK vK aK, square W is cW sW uW vW aW; the structure Input is the   *)
(* predicate oc983lf_input.  upper/lower are ABT_upper/ABT_lower; the       *)
(* scalar lemmas are C983LFS_* (C974LowerFaceScalars) and C983LFL_LARGE_HALF *)
(* (C974LowerFaceLarge); upper/lower_in_bands are C981SF_*_IN_BANDS;         *)
(* upper_self / lower_self are instances of ABT_OWNU.  Tag OC983LF_.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LowerFaceScalars.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LowerFaceLarge.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: Input (structure) *)
let oc983lf_input = new_definition
 `oc983lf_input cK sK uK vK aK cW sW uW vW aW <=>
    &1 < aW /\ aK = aW /\
    &0 < sK /\ sK <= cK /\ &4 * sK < &3 * cK /\
    &0 < sW /\ sW <= cW /\ &3 * sW < &2 * cW /\
    linside cK sK uK vK aK (&41 / &50) (&0) /\
    linside cK sK uK vK aK (&24 / &25) (--(&6) / &25) /\
    linside cW sW uW vW aW (&1) (&0) /\
    vK + aK <= &0 /\
    aK * cK - &1 <= sK * uK + cK * (vK + aK) /\
    uW + aW - cW <= cW /\
    vW + aW + sW <= cW / &2 /\
    ldisj cK sK uK vK aK cW sW uW vW aW`;;

(* Lean: separator_cone *)
let OC983LF_SEPARATOR_CONE = prove
 (`forall cK sK uK vK aK cW sW uW vW aW nx ny.
     cK * cK + sK * sK = &1 /\ &0 < aK /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     oc983lf_input cK sK uK vK aK cW sW uW vW aW /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cK sK uK vK aK nx ny <= ABT_lower cW sW uW vW aW nx ny
     ==> &0 < nx /\ &0 < nx + &6 * ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oc983lf_input] THEN STRIP_TAC THEN
  ABT_ALL_SB_TAC
   [[`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`], (`&41 / &50`, `&0`);
    [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`], (`&24 / &25`, `--(&6) / &25`);
    [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`], (`&1`, `&0`)]
   [`nx:real`, `ny:real`] THEN
  ABT_ARITH_TAC);;

(* Lean: separating_u *)
let OC983LF_SEPARATING_U = prove
 (`forall cK sK uK vK aK cW sW uW vW aW.
     cK * cK + sK * sK = &1 /\ &0 < aK /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     oc983lf_input cK sK uK vK aK cW sW uW vW aW
     ==> ABT_upper cK sK uK vK aK cK sK <= ABT_lower cW sW uW vW aW cK sK \/
         ABT_upper cK sK uK vK aK cW sW <= ABT_lower cW sW uW vW aW cW sW`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oc983lf_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aK:real = aW`)) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aW:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABT_ALL_SB_TAC
   [[`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aW:real`], (`&41 / &50`, `&0`);
    [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aW:real`], (`&24 / &25`, `--(&6) / &25`);
    [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`], (`&1`, `&0`)]
   [`cK:real`, `sK:real`; `--sK:real`, `cK:real`; `cW:real`, `sW:real`; `--sW:real`, `cW:real`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  ABT_ARITH_TAC);;

let OC983LF_NONNEG_CANCEL = prove
 (`forall y k. &0 < k /\ &0 <= y * k ==> &0 <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < --y * k` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let OC983LF_NEG_CANCEL = prove
 (`forall y k. &0 < k /\ y * k < &0 ==> y < &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= y * k` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let OC983LF_POS_CANCEL = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  MESON_TAC[REAL_LT_MUL_EQ]);;

let OC983LF_GEN_TAC tm v =
  REPEAT(FIRST_X_ASSUM(fun th -> if free_in tm (concl th) then MP_TAC th else NO_TAC)) THEN
  SPEC_TAC(tm, v) THEN GEN_TAC THEN REPEAT DISCH_TAC;;

let OC983LF_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_TAC];;

let OC983LF_VARS = [`cK:real`; `sK:real`; `cW:real`; `sW:real`; `x:real`; `z:real`];;

let OC983LF_IS_DIVEQ th =
  let t = concl th in
  is_eq t && is_var(lhand t) &&
  can (find_term (fun u -> try fst(dest_const u) = "real_div" with Failure _ -> false))
      (rand t);;

(* instantiate a scalar lemma at the half-angle variables, discharging its  *)
(* rational-form premises l = (1-x^2)/(1+x^2) etc. from the assumptions      *)
let OC983LF_PREP_TAC th =
  MP_TAC(SPECL OC983LF_VARS th) THEN
  ASSUM_LIST(fun ths -> REWRITE_TAC(map EQT_INTRO (filter OC983LF_IS_DIVEQ ths))) THEN
  DISCH_TAC;;

(* fire a prepared scalar lemma: prove its remaining premises *)
let OC983LF_FIRE_TAC th =
  let c = rand(concl(SPECL OC983LF_VARS th)) in
  FIRST_X_ASSUM(fun th' -> if is_imp(concl th') && rand(concl th') = c then
    MP_TAC th' THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); DISCH_TAC]
    else NO_TAC);;

let OC983LF_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: lower_face *)
let OC983LF_LOWER_FACE = prove
 (`forall cK sK uK vK aK cW sW uW vW aW.
     cK * cK + sK * sK = &1 /\ &0 < aK /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     oc983lf_input cK sK uK vK aK cW sW uW vW aW
     ==> --(sW / (&1 + cW)) * (&1 - sW) < uW - cW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    OC983LF_SEPARATING_U) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `oc983lf_input cK sK uK vK aK cW sW uW vW aW` THEN
  REWRITE_TAC[oc983lf_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aK:real = aW`)) THEN
  SUBGOAL_THEN `&0 < cK /\ &0 < cW` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cK pow 2 + sK pow 2 = &1 /\ cW pow 2 + sW pow 2 = &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cW sW uW vW aW (&1) (&0)`) THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  (* own-face supports *)
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aW:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  (* half-angle data *)
  OC983LF_USE C983LFS_HALF_DATA [`cK:real`; `sK:real`] THEN
  OC983LF_USE C983LFS_HALF_DATA [`cW:real`; `sW:real`] THEN
  SUBGOAL_THEN `sK / (&1 + cK) * (&1 + cK) = sK /\ sW / (&1 + cW) * (&1 + cW) = sW`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  OC983LF_GEN_TAC `sK / (&1 + cK)` `x:real` THEN
  OC983LF_GEN_TAC `sW / (&1 + cW)` `z:real` THEN
  MAP_EVERY OC983LF_PREP_TAC
   [C983LFS_SIGMA_IDENTITY; C983LFS_FORWARD_K_LARGE; C983LFS_FORWARD_K_SMALL;
    C983LFS_FORWARD_W_LARGE; C983LFS_FORWARD_W_SMALL; C983LFL_LARGE_HALF] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check OC983LF_IS_DIVEQ)) THEN
  SUBGOAL_THEN `sK < &1 /\ sW < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  OC983LF_PROD_TAC [`&0 < cK * cW`; `&0 < sK * sW`] THEN
  SUBGOAL_THEN `&0 < cK * cW + sK * sW` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  (* width *)
  SUBGOAL_THEN `&1 - x < uK + aW` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < uK + aW - (&1 - x) ==> &1 - x < uK + aW`) THEN
    MATCH_MP_TAC OC983LF_POS_CANCEL THEN EXISTS_TAC `sK:real` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    OC983LF_PROD_TAC [`&0 <= cK * --(vK + aW)`; `&0 < (aW - &1) * (cK + sK)`] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C983LFS_DENOMINATOR_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x * z` ASSUME_TAC THENL
   [OC983LF_PROD_TAC [`&0 < x * z`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* along K's u axis *)
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `ABT_upper cK sK uK vK aW cK sK = uK + aW`)) THEN
    ASM_CASES_TAC `z <= x` THENL
     [SUBGOAL_THEN `&0 <= sK * cW - cK * sW` ASSUME_TAC THENL
       [MATCH_MP_TAC OC983LF_NONNEG_CANCEL THEN
        EXISTS_TAC `(&1 + x pow 2) * (&1 + z pow 2)` THEN ASM_REWRITE_TAC[] THEN
        OC983LF_PROD_TAC [`&0 <= (x - z) * (&1 + x * z)`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `ABT_lower cW sW uW vW aW cK sK =
          cK + (cK * cW + sK * sW) * (uW - cW) + (sK * cW - cK * sW) * (vW + sW)`
      ASSUME_TAC THENL
       [REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
        SUBGOAL_THEN `abs(cK * cW + sK * sW) = cK * cW + sK * sW /\
                      abs(--cK * sW + sK * cW) = sK * cW - cK * sW`
          (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      OC983LF_PROD_TAC [`&0 <= (sK * cW - cK * sW) * (cW / &2 - (vW + sW + aW))`;
                        `&0 <= (sK * cW - cK * sW) * (aW - &1)`] THEN
      SUBGOAL_THEN `(sK * cW - cK * sW) * (&1 - cW / &2) - x * (&1 - sK) <
                    (cK * cW + sK * sW) * (uW - cW)` ASSUME_TAC THENL
       [RASM_ARITH_TAC; ALL_TAC] THEN
      OC983LF_FIRE_TAC C983LFS_FORWARD_K_LARGE THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < L - y ==> y < L`) THEN
      MATCH_MP_TAC OC983LF_POS_CANCEL THEN EXISTS_TAC `cK * cW + sK * sW` THEN
      CONJ_TAC THEN RASM_ARITH_TAC;
      SUBGOAL_THEN `x < z` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `sK * cW - cK * sW < &0` ASSUME_TAC THENL
       [MATCH_MP_TAC OC983LF_NEG_CANCEL THEN
        EXISTS_TAC `(&1 + x pow 2) * (&1 + z pow 2)` THEN ASM_REWRITE_TAC[] THEN
        OC983LF_PROD_TAC [`&0 < (z - x) * (&1 + x * z)`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `ABT_lower cW sW uW vW aW cK sK =
          cK + (cK * cW + sK * sW) * (uW - cW) + (sK * cW - cK * sW) * (vW + sW + aW)`
      ASSUME_TAC THENL
       [REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
        SUBGOAL_THEN `abs(cK * cW + sK * sW) = cK * cW + sK * sW /\
                      abs(--cK * sW + sK * cW) = --(sK * cW - cK * sW)`
          (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      OC983LF_PROD_TAC [`&0 < --(sK * cW - cK * sW) * (vW + sW + aW)`] THEN
      SUBGOAL_THEN `--x * (&1 - sK) < (cK * cW + sK * sW) * (uW - cW)` ASSUME_TAC THENL
       [RASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `z <= &2 / &7` THENL
       [OC983LF_FIRE_TAC C983LFS_FORWARD_K_SMALL THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < L - y ==> y < L`) THEN
        MATCH_MP_TAC OC983LF_POS_CANCEL THEN EXISTS_TAC `cK * cW + sK * sW` THEN
        CONJ_TAC THEN RASM_ARITH_TAC;
        OC983LF_USE C983LFS_COSINE_LOWER [`cW:real`; `sW:real`] THEN
        OC983LF_FIRE_TAC C983LFL_LARGE_HALF THEN
        OC983LF_PROD_TAC [`&0 < (cK * cW + sK * sW) * ((cW - &1) - (uW - cW))`] THEN
        RASM_ARITH_TAC]];
    (* along W's u axis *)
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `ABT_lower cW sW uW vW aW cW sW = uW`)) THEN
    ASM_CASES_TAC `z <= x` THENL
     [SUBGOAL_THEN `&0 <= sK * cW - cK * sW` ASSUME_TAC THENL
       [MATCH_MP_TAC OC983LF_NONNEG_CANCEL THEN
        EXISTS_TAC `(&1 + x pow 2) * (&1 + z pow 2)` THEN ASM_REWRITE_TAC[] THEN
        OC983LF_PROD_TAC [`&0 <= (x - z) * (&1 + x * z)`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `ABT_upper cK sK uK vK aW cW sW =
          (cK * cW + sK * sW) * (uK + aW) + (sK * cW - cK * sW) * (aW - (vK + aW))`
      ASSUME_TAC THENL
       [REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
        SUBGOAL_THEN `abs(cW * cK + sW * sK) = cK * cW + sK * sW /\
                      abs(--cW * sK + sW * cK) = sK * cW - cK * sW`
          (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
      OC983LF_PROD_TAC [`&0 < (cK * cW + sK * sW) * ((uK + aW) - (&1 - x))`;
                        `&0 <= (sK * cW - cK * sW) * (aW - (vK + aW) - &1)`] THEN
      OC983LF_FIRE_TAC C983LFS_FORWARD_W_LARGE THEN
      RASM_ARITH_TAC;
      SUBGOAL_THEN `x < z` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `sK * cW - cK * sW < &0` ASSUME_TAC THENL
       [MATCH_MP_TAC OC983LF_NEG_CANCEL THEN
        EXISTS_TAC `(&1 + x pow 2) * (&1 + z pow 2)` THEN ASM_REWRITE_TAC[] THEN
        OC983LF_PROD_TAC [`&0 < (z - x) * (&1 + x * z)`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `ABT_upper cK sK uK vK aW cW sW =
          (cK * cW + sK * sW) * (uK + aW) - (sK * cW - cK * sW) * (vK + aW)`
      ASSUME_TAC THENL
       [REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
        SUBGOAL_THEN `abs(cW * cK + sW * sK) = cK * cW + sK * sW /\
                      abs(--cW * sK + sW * cK) = --(sK * cW - cK * sW)`
          (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(cK * cW + sK * sW) * (&1 - x) < ABT_upper cK sK uK vK aW cW sW`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < A - B ==> B < A`) THEN
        MATCH_MP_TAC OC983LF_POS_CANCEL THEN EXISTS_TAC `sK:real` THEN
        ASM_REWRITE_TAC[] THEN
        OC983LF_PROD_TAC
         [`&0 <= (cK * cW + sK * sW) * ((sK * uK + cK * (vK + aW)) - (aW * cK - &1))`;
          `&0 <= cW * --(vK + aW)`;
          `&0 < (cK * cW + sK * sW) * (aW - &1)`] THEN
        SUBGOAL_THEN `&0 < ((cK * cW + sK * sW) * (aW - &1)) * (cK + sK)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN
         `sK * (((cK * cW + sK * sW) * (uK + aW) - (sK * cW - cK * sW) * (vK + aW)) -
                (cK * cW + sK * sW) * (&1 - x)) =
          (cK * cW + sK * sW) * ((sK * uK + cK * (vK + aW)) - (aW * cK - &1)) -
          cW * (vK + aW) + ((cK * cW + sK * sW) * (aW - &1)) * (cK + sK)`
        SUBST1_TAC THENL
         [UNDISCH_TAC `cK * cK + sK * sK = &1` THEN
          UNDISCH_TAC `sK * x = &1 - cK` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
        RASM_ARITH_TAC; ALL_TAC] THEN
      OC983LF_FIRE_TAC C983LFS_FORWARD_W_SMALL THEN
      RASM_ARITH_TAC]]);;
