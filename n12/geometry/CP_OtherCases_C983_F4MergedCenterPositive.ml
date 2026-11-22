(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4MergedCenterPositive.lean    *)
(* (N12Compact.Completion.OtherCases.C983.F4MergedCenter, sections 4-5).     *)
(* Conventions of CP_OtherCases_C983_F4MergedCenter.ml (Input W K =          *)
(* c983fmc_input, statements via c983fmc_stmt with the OpenSquare invariants *)
(* of W and K explicit).  Lean `upper` / `lower` are ABT_upper / ABT_lower;  *)
(* WallProfile.upper_in_bands = OCWPSG_UPPER_IN_BANDS, C981 lower_in_bands = *)
(* C981SF_LOWER_IN_BANDS, WallProfile.vertex = OCWPVG_VERTEX,                *)
(* DerivedWalls.closed_affine_bound = OCDW_CLOSED_AFFINE_BOUND.              *)
(* PositiveComparisons d r is c983fmcp_comparisons d r (an explicit premise, *)
(* as in Lean).  (Lean header: "no compiler replay has been performed".)     *)
(* Tag C983FMCP_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4MergedCenter.ml";;
needs "n12/geometry/CP_OtherCases_DerivedWalls.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;

(* Lean: PositiveComparisons *)
let c983fmcp_comparisons = new_definition
 `c983fmcp_comparisons (d:real) (r:real) <=>
    (forall b t. &0 < b /\ &0 <= t /\ t <= b /\ b pow 2 + t pow 2 = &1
       ==> &1 + (r - &1) / d - &43 / &500 * r <=
           (d * b + r * t) + (r - (d * b + r * t)) / b - &43 / &500 * r + max (d * t - r * b) (&0)) /\
    (forall b t. &0 < b /\ &0 <= t /\ t <= b /\ b pow 2 + t pow 2 = &1 /\ &0 <= r * b - d * t
       ==> &0 < &1 - b - t + (t - &1) / b - &43 / &500 * t + (d * b + r * t) +
                &7 / &20 * (r * b - d * t) * (d + r)) /\
    (forall b t. &0 < b /\ &0 <= t /\ t <= b /\ b pow 2 + t pow 2 = &1 /\ &0 <= d * t - r * b
       ==> &0 < &1 - b - t + (t - &1) / b - &43 / &500 * t + (d * b + r * t) +
                &7 / &20 * (d * t - r * b) * (d - r))`;;

let C983FMCP_LIN = NLIN_TAC ~deg2:false [];;
let C983FMCP_FACT = C983FMC_FACT;;

(* removes each abs(t) of the goal by the sign of t (decided by LP from the
   assumptions), then closes the polynomial identity by REAL_RING *)
let C983FMCP_ABS_TAC (asl, w as gl) =
  let abss = setify (find_terms (fun t -> is_comb t && rator t = `abs:real->real`) w) in
  let rw t =
    let a = rand t in
    try MP (SPEC a (REAL_ARITH `forall x. &0 <= x ==> abs x = x`))
           (TAC_PROOF((asl, mk_binop `(<=):real->real->bool` `&0` a), NLIN_TAC ~deg2:false []))
    with Failure _ ->
      MP (SPEC a (REAL_ARITH `forall x. x <= &0 ==> abs x = --x`))
         (TAC_PROOF((asl, mk_binop `(<=):real->real->bool` a `&0`), NLIN_TAC ~deg2:false [])) in
  (REWRITE_TAC (map rw abss) THEN CONV_TAC REAL_RING) gl;;

(* x / y as a fresh variable q with y * q = x *)
let C983FMCP_DIV_TAC tm q =
  ABBREV_TAC (mk_eq(q, tm)) THEN
  SUBGOAL_THEN (mk_eq(mk_binop `( * ):real->real->real` (rand tm) q, lhand tm)) ASSUME_TAC THENL
   [EXPAND_TAC (fst (dest_var q)) THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN RASM_ARITH_TAC;
    ALL_TAC];;

(* Lean: joining_margin *)
let C983FMCP_JOINING_MARGIN = prove
 (`forall d r z. &0 < d /\ &0 < r /\ d pow 2 + r pow 2 = &1 /\ r * z = &1 - d /\
           z * (&1 + d) = r /\ &1 / &4 <= z /\ z <= &13 / &50
           ==> &0 < &1 + (r - &1) / d - &43 / &500 * r - (d + r - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983FMCP_FACT `&0 < -- &2 * z * z + &793 / &500 * z + &793 / &2000` (NLIN_TAC []) THEN
  C983FMCP_FACT `&0 < -- &2 * z * z * z + &1043 / &500 * z * z - &43 / &500`
    (SUBGOAL_THEN `-- &2 * z * z * z + &1043 / &500 * z * z - &43 / &500 - &21 / &1600 =
                   (z - &1 / &4) * (-- &2 * z * z + &793 / &500 * z + &793 / &2000)` ASSUME_TAC THENL
      [CONV_TAC REAL_RING; ALL_TAC] THEN
     C983FMCP_FACT `&0 <= (z - &1 / &4) * (-- &2 * z * z + &793 / &500 * z + &793 / &2000)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     RASM_ARITH_TAC) THEN
  C983FMCP_FACT `r * (&1 + z * z) = &2 * z`
    (UNDISCH_TAC `r * z = &1 - d` THEN UNDISCH_TAC `z * (&1 + d) = r` THEN CONV_TAC REAL_RING) THEN
  ABBREV_TAC `X = &2 * d + r - &1 - d * d - &543 / &500 * d * r` THEN
  C983FMCP_FACT `(&1 + z * z) * X = r * (-- &2 * z * z * z + &1043 / &500 * z * z - &43 / &500)`
    (EXPAND_TAC "X" THEN UNDISCH_TAC `r * z = &1 - d` THEN
     UNDISCH_TAC `r * (&1 + z * z) = &2 * z` THEN CONV_TAC REAL_RING) THEN
  C983FMCP_FACT `&0 < (&1 + z * z) * X`
    (ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]) THEN
  C983FMCP_FACT `&0 < X`
    (FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `&0 < (&1 + z * z) * X`)) THEN
     MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN MATCH_MP_TAC (CONJUNCT1 REAL_LT_MUL_EQ) THEN
     MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC) THEN
  SUBGOAL_THEN `&1 + (r - &1) / d - &43 / &500 * r - (d + r - &1) = X / d` SUBST1_TAC THENL
   [EXPAND_TAC "X" THEN UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]]);;

(* Lean: positive_singleton_faces *)
let C983FMCP_POSITIVE_SINGLETON_FACES = prove
 (c983fmc_stmt ["&0 < cK"; "&0 <= sK"; "sK <= cK"]
    "aK - &43 / &500 * cK <= vK + aK + cK - sK /\\
     cK * (uK + aK + cK + sK) >= cK * aK + sK * (vK + aK + cK - sK) - &1",
  C983FMC_OPEN_TAC THEN
  MP_TAC(SPECL (C983FMC_K @ [`&1`; `&0`; `--(&2)`; `--(&1)`; `--(&1)`;
                `cK * uK - sK * (vK + aK)`; `sK * uK + cK * (vK + aK)`]) OCDW_CLOSED_AFFINE_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_RID] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC OCWPVG_VERTEX THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC];
    DISCH_TAC] THEN
  C983FMC_UNFOLD_TAC THEN
  C983FMCP_FACT `sK - &543 / &500 * cK <= vK`
    (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C983FMC_MISS_TAC `~linside cK sK uK vK aK (--(&1)) (--(&543 / &500))`) THEN
  CONJ_TAC THEN REWRITE_TAC[real_ge] THEN C983FMCP_LIN);;

(* the shared opening of singleton_positive_w / _u *)
let C983FMCP_EXTRA =
  C983FMC_ORIENT @ ["&0 < cK"; "&0 <= sK"; "sK <= cK"; "c983fmcp_comparisons cW sW"];;

(* Lean: singleton_positive_w *)
let C983FMCP_SINGLETON_POSITIVE_W = prove
 (c983fmc_stmt (C983FMCP_EXTRA @
    ["ABT_upper cK sK uK vK aK cW sW <= ABT_lower cW sW uW vW aW cW sW"]) "F",
  C983FMC_OPEN_TAC THEN C983FMC_USE C983FMC_ANGLE_WINDOW THEN
  C983FMC_USE C983FMCP_POSITIVE_SINGLETON_FACES THEN C983FMC_USE C983FMC_MISSING_FACES THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c983fmcp_comparisons] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c983fmcp_comparisons`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cK:real`; `sK:real`] o
    check (fun th -> not (can (find_term ((=) `&7 / &20`)) (concl th)) &&
                     can (find_term ((=) `max`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `sW / (&1 + cW)`] C983FMCP_JOINING_MARGIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    MATCH_MP_TAC REAL_DIV_RMUL THEN RASM_ARITH_TAC;
    DISCH_TAC] THEN
  C983FMCP_FACT `ABT_lower cW sW uW vW aW cW sW = uW`
    (ASM_REWRITE_TAC[C981SF_LOWER_IN_BANDS; REAL_ARITH `--cW * sW + sW * cW = &0`] THEN
     REAL_ARITH_TAC) THEN
  C983FMCP_FACT `&0 < cW * cK + sW * sK` (NLIN_TAC []) THEN
  C983FMCP_FACT
   `ABT_upper cK sK uK vK aK cW sW + (cW + sW) =
    (cW * cK + sW * sK) * (uK + aK + cK + sK) + (sW * cK - cW * sK) * (vK + aK + cK - sK) +
    aK * max (cW * sK - sW * cK) (&0)`
    (REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
     SUBGOAL_THEN `cW * (cK * cK + sK * sK) = cW /\ sW * (cK * cK + sK * sK) = sW` MP_TAC THENL
      [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
     UNDISCH_TAC `&0 < cW * cK + sW * sK` THEN REAL_ARITH_TAC) THEN
  ABBREV_TAC `g = max (cW * sK - sW * cK) (&0)` THEN
  C983FMCP_FACT `&0 <= g /\ cW * sK - sW * cK <= g` (EXPAND_TAC "g" THEN REAL_ARITH_TAC) THEN
  C983FMCP_DIV_TAC `(sW - (cW * cK + sW * sK)) / cK` `q:real` THEN
  C983FMCP_DIV_TAC `(sW - &1) / cW` `p:real` THEN
  ABBREV_TAC `U = ABT_upper cK sK uK vK aK cW sW` THEN
  C983FMCP_FACT `(cW * cK + sW * sK) * sK + cK * (sW * cK - cW * sK) = sW`
    (SUBGOAL_THEN `sW * (cK * cK + sK * sK) = sW` MP_TAC THENL
      [ASM_REWRITE_TAC[REAL_MUL_RID]; REAL_ARITH_TAC]) THEN
  C983FMCP_FACT `&0 <= (cW * cK + sW * sK) *
     (cK * (uK + aK + cK + sK) - (cK * aK + sK * (vK + aK + cK - sK) - &1))`
    (MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC) THEN
  C983FMCP_FACT `&0 <= sW * ((vK + aK + cK - sK) - (aK - &43 / &500 * cK))`
    (MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC) THEN
  C983FMCP_FACT `&0 < cK * (cW * cK + sW * sK)` (MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]) THEN
  C983FMCP_FACT `&0 <= cK * g` (MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC) THEN
  C983FMCP_FACT `&0 < (aK - &1) * (cK * (cW * cK + sW * sK) + sW + cK * g)`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCP_LIN) THEN
  C983FMCP_FACT `((cW * cK + sW * sK) * sK + cK * (sW * cK - cW * sK)) * (vK + aK + cK - sK) =
                 sW * (vK + aK + cK - sK)` (ASM_REWRITE_TAC[]) THEN
  C983FMCP_FACT `cK * ((cW * cK + sW * sK) + q - &43 / &500 * sW + g) < cK * (U + (cW + sW))`
    (ASM_REWRITE_TAC[] THEN C983FMCP_LIN) THEN
  C983FMCP_FACT `(cW * cK + sW * sK) + q - &43 / &500 * sW + g < U + (cW + sW)`
    (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_lt" (concl th) &&
       can (find_term ((=) `q:real`)) (concl th))) THEN
     ASM_SIMP_TAC[REAL_LT_LMUL_EQ]) THEN
  C983FMCP_LIN);;

(* Lean: singleton_positive_u *)
let C983FMCP_SINGLETON_POSITIVE_U = prove
 (c983fmc_stmt (C983FMCP_EXTRA @
    ["ABT_upper cK sK uK vK aK cK sK <= ABT_lower cW sW uW vW aW cK sK"]) "F",
  C983FMC_OPEN_TAC THEN
  C983FMC_USE C983FMCP_POSITIVE_SINGLETON_FACES THEN C983FMC_USE C983FMC_MISSING_FACES THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c983fmcp_comparisons] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c983fmcp_comparisons`)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall (concl th) &&
      can (find_term ((=) `(t - &1) / b`)) (concl th)
    then MP_TAC(SPECL [`cK:real`; `sK:real`] th) else NO_TAC) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC) THEN
  C983FMCP_FACT `ABT_upper cK sK uK vK aK cK sK = uK + aK`
    (ASM_REWRITE_TAC[OCWPSG_UPPER_IN_BANDS; REAL_ARITH `--cK * sK + sK * cK = &0`] THEN
     REAL_ARITH_TAC) THEN
  C983FMCP_DIV_TAC `(sK - &1) / cK` `p:real` THEN
  C983FMCP_FACT `&0 <= sK * ((vK + aK + cK - sK) - (aK - &43 / &500 * cK))`
    (MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC) THEN
  C983FMCP_FACT `&0 < (aK - &1) * (cK + sK)` (MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC) THEN
  C983FMCP_FACT `&0 < cK * ((uK + aK) - (&1 - cK - sK + p - &43 / &500 * sK))` C983FMCP_LIN THEN
  C983FMCP_FACT `&1 - cK - sK + p - &43 / &500 * sK < uK + aK`
    (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_lt" (concl th) &&
       can (find_term ((=) `p:real`)) (concl th))) THEN
     ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN REAL_ARITH_TAC) THEN
  C983FMCP_FACT `&0 < cW * cK + sW * sK` (NLIN_TAC []) THEN
  C983FMCP_FACT `&0 < (cW * cK + sW * sK) * (--(&1) - uW)`
    (MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC) THEN
  C983FMC_UNFOLD_TAC THEN
  ASM_CASES_TAC `&0 <= sW * cK - cW * sK` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      lhand (concl th) = `&0 <= sW * cK - cW * sK`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    C983FMCP_FACT `&0 <= (sW * cK - cW * sK) * ((vW + aW) - &7 / &20 * (cW + sW))`
      (MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN C983FMCP_LIN) THEN
    C983FMCP_FACT `ABT_lower cW sW uW vW aW cK sK =
        (cW * cK + sW * sK) * uW - (sW * cK - cW * sK) * (vW + aW)`
      (REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
       C983FMCP_ABS_TAC) THEN
    C983FMCP_LIN;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      lhand (concl th) = `&0 <= cW * sK - sW * cK`)) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
    C983FMCP_FACT `&0 <= cW * sK - sW * cK` RASM_ARITH_TAC THEN
    C983FMCP_FACT `&0 <= (cW * sK - sW * cK) * (--(&7 / &20) * (cW - sW) - vW)`
      (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMCP_LIN) THEN
    C983FMCP_FACT `ABT_lower cW sW uW vW aW cK sK =
        (cW * cK + sW * sK) * uW + (cW * sK - sW * cK) * vW`
      (REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
       C983FMCP_ABS_TAC) THEN
    C983FMCP_LIN]);;
