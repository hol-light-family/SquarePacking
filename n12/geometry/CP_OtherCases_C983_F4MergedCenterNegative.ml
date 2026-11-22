(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4MergedCenterNegative.lean    *)
(* (N12Compact.Completion.OtherCases.C983.F4MergedCenter, sections 6-7).     *)
(* Conventions of CP_OtherCases_C983_F4MergedCenter.ml (Input W K =          *)
(* c983fmc_input, statements via c983fmc_stmtv with the OpenSquare           *)
(* invariants of W and K explicit).  Lean `upper` / `lower` / strict_bounds  *)
(* are ABT_upper / ABT_lower / ABT_STRICT_BOUNDS; WallProfile.upper_in_bands *)
(* = OCWPSG_UPPER_IN_BANDS, C981 lower_in_bands = C981SF_LOWER_IN_BANDS,     *)
(* WallProfile.upper_neg / lower_neg = OCWPVG_UPPER_NEG / OCWPVG_LOWER_NEG;  *)
(* CongruentSAT.faceSeparation_of_disjoint + separated + parallel_radius /   *)
(* transverse_radius = ABT_FOUR_AXES.                                        *)
(* (Lean header: "no compiler replay has been performed".)  Tag C983FMCN_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4MergedCenter.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;

let C983FMCN_LIN = NLIN_TAC ~deg2:false [];;
let C983FMCN_FACT = C983FMC_FACT;;

(* removes each abs(t) of the goal by the sign of t (decided by LP from the
   assumptions), then closes the polynomial identity by REAL_RING *)
let C983FMCN_ABS_TAC (asl, w as gl) =
  let abss = setify (find_terms (fun t -> is_comb t && rator t = `abs:real->real`) w) in
  let rw t =
    let a = rand t in
    try MP (SPEC a (REAL_ARITH `forall x. &0 <= x ==> abs x = x`))
           (TAC_PROOF((asl, mk_binop `(<=):real->real->bool` `&0` a), NLIN_TAC ~deg2:false []))
    with Failure _ ->
      MP (SPEC a (REAL_ARITH `forall x. x <= &0 ==> abs x = --x`))
         (TAC_PROOF((asl, mk_binop `(<=):real->real->bool` a `&0`), NLIN_TAC ~deg2:false [])) in
  (REWRITE_TAC (map rw abss) THEN CONV_TAC REAL_RING) gl;;

(* Lean: normal_coefficients (private) *)
let C983FMCN_NORMAL_COEFFICIENTS = prove
 (`forall d r b t. &0 < d /\ &0 < r /\ r < d /\ &0 < b /\ &0 <= t /\ t <= b
             ==> &0 < d * b - r * t /\ &0 < d * t + r * b`,
  REPEAT STRIP_TAC THENL
   [C983FMCN_FACT `&0 < (d - r) * b` (MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC) THEN
    C983FMCN_FACT `&0 <= r * (b - t)` (MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
    C983FMCN_LIN;
    MATCH_MP_TAC REAL_LET_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC]);;

let C983FMCN_K = [`cK:real`; `--t`; `uK:real`; `vK:real`; `aK:real`];;
let C983FMCN_NEG = C983FMC_ORIENT @ ["sK = --t"; "&0 < cK"; "&0 <= t"; "t <= cK"];;

(* common opening: angle window (z abbreviated), missing faces, sK := --t, *)
(* the two normal coefficients                                            *)
let C983FMCN_OPEN_TAC =
  C983FMC_OPEN_TAC THEN C983FMC_USE C983FMC_ANGLE_WINDOW THEN C983FMC_USE C983FMC_MISSING_FACES THEN
  ABBREV_TAC `z = sW / (&1 + cW)` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sK = --t`)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `cK:real`; `t:real`] C983FMCN_NORMAL_COEFFICIENTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  C983FMCN_FACT `cK pow 2 + t pow 2 = &1`
    (UNDISCH_TAC `cK * cK + --t * --t = &1` THEN CONV_TAC REAL_RING);;

(* Lean: singleton_negative_u *)
let C983FMCN_SINGLETON_NEGATIVE_U = prove
 (c983fmc_stmtv " t" (C983FMCN_NEG @
    ["ABT_upper cK sK uK vK aK cK (--t) <= ABT_lower cW sW uW vW aW cK (--t)"]) "F",
  C983FMCN_OPEN_TAC THEN
  C983FMCN_FACT `ABT_lower cW sW uW vW aW cK (--t) =
      (cW * cK - sW * t) * uW - (sW * cK + cW * t) * (vW + aW)`
    (REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
     C983FMCN_ABS_TAC) THEN
  MP_TAC(SPECL (C983FMCN_K @ [`--(&1)`; `--(&1)`; `cK:real`; `--t`]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cK pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
    STRIP_TAC] THEN
  C983FMC_UNFOLD_TAC THEN
  C983FMCN_FACT `&7 / &20 * (cW + sW) < vW + aW` C983FMCN_LIN THEN
  C983FMCN_FACT `&0 < (cW * cK - sW * t) * (--(&1) - uW)`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&0 < (sW * cK + cW * t) * ((vW + aW) - &7 / &20 * (cW + sW))`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&0 < sW * (&7 / &20 * (cW + sW) - z)`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&0 < cW - &1 + &7 / &20 * sW * (cW + sW)` C983FMCN_LIN THEN
  C983FMCN_FACT `&0 < cW * (cW + sW)` (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&0 < &1 - sW + &7 / &20 * cW * (cW + sW)` C983FMCN_LIN THEN
  C983FMCN_FACT `&0 < cK * (cW - &1 + &7 / &20 * sW * (cW + sW))`
    (MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]) THEN
  C983FMCN_FACT `&0 <= t * (&1 - sW + &7 / &20 * cW * (cW + sW))`
    (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_LIN);;

(* Lean: singleton_negative_v *)
let C983FMCN_SINGLETON_NEGATIVE_V = prove
 (c983fmc_stmtv " t" (C983FMCN_NEG @
    ["ABT_upper cK sK uK vK aK t cK <= ABT_lower cW sW uW vW aW t cK"]) "F",
  C983FMCN_OPEN_TAC THEN
  C983FMCN_FACT `ABT_lower cW sW uW vW aW t cK =
      (cW * t + sW * cK) * uW + (cW * cK - sW * t) * vW`
    (REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
     C983FMCN_ABS_TAC) THEN
  MP_TAC(SPECL (C983FMCN_K @ [`--(&31 / &25)`; `--(&13 / &100)`; `t:real`; `cK:real`]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cK pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
    STRIP_TAC] THEN
  C983FMC_UNFOLD_TAC THEN
  C983FMCN_FACT `vW < --(&7 / &20) * (cW - sW)` C983FMCN_LIN THEN
  C983FMCN_FACT `&0 < (cW * t + sW * cK) * (--(&1) - uW)`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&0 < (cW * cK - sW * t) * (--(&7 / &20) * (cW - sW) - vW)`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `cW <= &1` (NLIN_TAC [SQ_NONNEG `sW:real`]) THEN
  C983FMCN_FACT `&0 < sW * (cW - sW)` (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `cW - &7 / &20 * sW * (cW - sW) - &31 / &25 < &0` C983FMCN_LIN THEN
  C983FMCN_FACT `(&19 / &50) * (&19 / &50) < (cW - sW) * (cW - sW)`
    (MATCH_MP_TAC REAL_LT_MUL2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&0 < (sW + &7 / &20 * cW * (cW - sW) - &13 / &100) +
                      (cW - &7 / &20 * sW * (cW - sW) - &31 / &25)` C983FMCN_LIN THEN
  C983FMCN_FACT `&0 < cK * ((sW + &7 / &20 * cW * (cW - sW) - &13 / &100) +
                      (cW - &7 / &20 * sW * (cW - sW) - &31 / &25))`
    (MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]) THEN
  C983FMCN_FACT `&0 <= (cK - t) * --(cW - &7 / &20 * sW * (cW - sW) - &31 / &25)`
    (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_LIN);;

(* Lean: negative_singleton_chord *)
let C983FMCN_NEGATIVE_SINGLETON_CHORD = prove
 (`forall d r b t z. &0 < d /\ &0 < r /\ d pow 2 + r pow 2 = &1 /\
     &0 < b /\ &0 <= t /\ t <= b /\ b pow 2 + t pow 2 = &1 /\
     &1 / &4 < z /\ r * z = &1 - d /\ &87 / &100 < d /\ &47 / &100 < r
     ==> d + r - &1 < (d * t + r * b) * (&87 / &100 * b - &6 / &25 * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983FMCN_FACT `&0 <= b * b - t * t`
    (REWRITE_TAC[REAL_ARITH `b * b - t * t = (b - t) * (b + t)`] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
  C983FMCN_FACT `&0 <= &2 * b * t`
    (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]) THEN
  C983FMCN_FACT `(b * b - t * t) pow 2 + (&2 * b * t) pow 2 = &1`
    (UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING) THEN
  ABBREV_TAC `x = b * b - t * t` THEN ABBREV_TAC `y = &2 * b * t` THEN
  C983FMCN_FACT `&1 <= x + y`
    (C983FMCN_FACT `&0 <= x * y` (MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]) THEN
     REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C983FMCN_FACT `(x + y) * (x + y) < &1 * &1`
       (MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC) THEN
     UNDISCH_TAC `x pow 2 + y pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&0 <= &28 / &25 * d + &113 / &200 * r - &1` C983FMCN_LIN THEN
  C983FMCN_FACT `&0 < r * (z - &13 / &100)` (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&28 / &25 * d + &113 / &200 * r - &1 < &87 / &200 * r + &3 / &25 * d` C983FMCN_LIN THEN
  C983FMCN_FACT `(d + r) pow 2 <= &2` (NLIN_TAC [SQ_NONNEG `d - r:real`]) THEN
  C983FMCN_FACT `&0 < &1 - &137 / &200 * (d + r)`
    (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
     C983FMCN_FACT `(&200 / &137) * (&200 / &137) <= (d + r) * (d + r)`
       (MATCH_MP_TAC REAL_LE_MUL2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN C983FMCN_LIN) THEN
     UNDISCH_TAC `(d + r) pow 2 <= &2` THEN REWRITE_TAC[REAL_POW_2] THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&28 / &25 * d + &113 / &200 * r - &1 < &87 / &200 * d - &3 / &25 * r` C983FMCN_LIN THEN
  C983FMCN_FACT `&0 < x * ((&87 / &200 * r + &3 / &25 * d) - (&28 / &25 * d + &113 / &200 * r - &1)) +
                      y * ((&87 / &200 * d - &3 / &25 * r) - (&28 / &25 * d + &113 / &200 * r - &1))`
    (DISJ_CASES_TAC(MP (REAL_ARITH `&0 <= x ==> &0 < x \/ x = &0`) (ASSUME `&0 <= x`)) THENL
      [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
       CONJ_TAC THEN C983FMCN_LIN;
       ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
       MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN]) THEN
  C983FMCN_FACT `&0 <= (&28 / &25 * d + &113 / &200 * r - &1) * (x + y - &1)`
    (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `(d * t + r * b) * (&87 / &100 * b - &6 / &25 * t) - (d + r - &1) =
     (&87 / &200 * r + &3 / &25 * d) * x + (&87 / &200 * d - &3 / &25 * r) * y -
     (&28 / &25 * d + &113 / &200 * r - &1)`
    (EXPAND_TAC "x" THEN EXPAND_TAC "y" THEN
     UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING) THEN
  C983FMCN_LIN);;

(* Lean: singleton_negative_w *)
let C983FMCN_SINGLETON_NEGATIVE_W = prove
 (c983fmc_stmtv " t" (C983FMCN_NEG @
    ["ABT_upper cK sK uK vK aK cW sW <= ABT_lower cW sW uW vW aW cW sW"]) "F",
  C983FMCN_OPEN_TAC THEN
  C983FMCN_FACT `ABT_upper cK (--t) uK vK aK cW sW =
      (cW * cK - sW * t) * (uK + aK) + (cW * t + sW * cK) * (vK + aK)`
    (REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
     C983FMCN_ABS_TAC) THEN
  C983FMCN_FACT `ABT_lower cW sW uW vW aW cW sW = uW`
    (ASM_REWRITE_TAC[C981SF_LOWER_IN_BANDS; REAL_ARITH `--cW * sW + sW * cW = &0`] THEN
     REAL_ARITH_TAC) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `cK:real`; `t:real`; `z:real`]
    C983FMCN_NEGATIVE_SINGLETON_CHORD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[REAL_POW_2]; RASM_ARITH_TAC]; DISCH_TAC] THEN
  C983FMCN_FACT `(cW * cK - sW * t) * (--cK + t) +
        (cW * t + sW * cK) * (--(&31 / &25) * t - &13 / &100 * cK) =
      --(cW + sW) + (cW * t + sW * cK) * (&87 / &100 * cK - &6 / &25 * t)`
    (UNDISCH_TAC `cK pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING) THEN
  C983FMC_UNFOLD_TAC THEN
  C983FMCN_FACT `&0 < (cW * cK - sW * t) * ((uK + aK) - (--cK + t))`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_FACT `&0 < (cW * t + sW * cK) * ((vK + aK) - (--(&31 / &25) * t - &13 / &100 * cK))`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMCN_LIN) THEN
  C983FMCN_LIN);;

(* Lean: nonpositive_singleton_impossible *)
let C983FMCN_NONPOSITIVE_SINGLETON_IMPOSSIBLE = prove
 (c983fmc_stmtv " t" C983FMCN_NEG "F",
  C983FMC_OPEN_TAC THEN
  MP_TAC(SPECL (C983FMC_K @ C983FMC_W) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM(ACCEPT_TAC o SYM)]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sK = --t`)) THEN
  let wk = C983FMC_W @ [`cK:real`; `--t`; `uK:real`; `vK:real`; `aK:real`; `t:real`] in
  let close th = MATCH_MP_TAC (SPECL wk th) THEN REPEAT CONJ_TAC THEN
                 FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC] in
  let unit_tac =
    REWRITE_TAC[REAL_POW_2] THEN
    UNDISCH_TAC `cK * cK + --t * --t = &1` THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
    CONV_TAC REAL_RING in
  (* the separator cone at (nx, ny), the separation goal given as an assumption *)
  let cone nx ny =
    MP_TAC(SPECL (C983FMC_W @ [`cK:real`; `--t`; `uK:real`; `vK:real`; `aK:real`; nx; ny])
             C983FMC_SEPARATOR_CONE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC; unit_tac;
             REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG; REAL_LE_NEG2] THEN
             FIRST_ASSUM ACCEPT_TAC];
      STRIP_TAC THEN RASM_ARITH_TAC] in
  let ng x = mk_comb(`(--):real->real`, x) in
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC))) THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [close C983FMCN_SINGLETON_NEGATIVE_U; cone (ng `cK:real`) (ng `--t`)];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REAL_NEG_NEG]) THEN DISCH_TAC THEN
      close C983FMCN_SINGLETON_NEGATIVE_V;
      cone (ng `-- --t`) (ng `cK:real`)];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [close C983FMCN_SINGLETON_NEGATIVE_W; cone (ng `cW:real`) (ng `sW:real`)];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [cone `--sW` `cW:real`; cone (ng `--sW`) (ng `cW:real`)]]);;
