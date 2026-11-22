(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4MergedCenterEnding.lean      *)
(* (N12Compact.Completion.OtherCases.C983.F4MergedCenter).  Assembly of      *)
(* C983-F4-MERGED-CENTER.md.  Conventions of CP_OtherCases_C983_             *)
(* F4MergedCenter.ml (Input W K = c983fmc_input, OpenSquare invariants       *)
(* explicit, statements via c983fmc_stmt).  positive_comparisons =           *)
(* C983FMCM_POSITIVE_COMPARISONS, singleton_positive_u / w = C983FMCP_*,     *)
(* nonpositive_singleton_impossible = C983FMCN_*, separator_cone /           *)
(* angle_window / actual_input = C983FMC_*, CongruentSAT face separation +   *)
(* separated + parallel/transverse_radius = ABT_FOUR_AXES, WallProfile.      *)
(* upper_neg / lower_neg = OCWPVG_UPPER_NEG / LOWER_NEG, ClosedFrames.       *)
(* canonical_frame = CLF_CANONICAL_FRAME, MergedLeftNegative.point = MLN_POINT,*)
(* merged_no_f3 = C983MTE_MERGED_NO_F3, left_aux = C983AB_LEFT_AUX.          *)
(* owners p 1 / 7 / 8 = owner 2 / 2304 / 4096; q.translated 2 2 = c983fmc_tr.*)
(* (Lean header: "source-only and uncompiled".)  Tag C983FMCE_.              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4MergedCenterNegative.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4MergedCenterPositive.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4MergedCenterMonotone.ml";;
needs "n12/geometry/CP_OtherCases_C983_MergedCenterF5.ml";;

(* Lean: Input.reframe_right *)
let C983FMCE_INPUT_REFRAME_RIGHT = prove
 (`forall cW sW uW vW aW cK sK uK vK aK cR sR uR vR aR.
     c983fmc_input cW sW uW vW aW cK sK uK vK aK /\ aR = aK /\
     (forall x y. linside cR sR uR vR aR x y <=> linside cK sK uK vK aK x y)
     ==> c983fmc_input cW sW uW vW aW cR sR uR vR aR`,
  REWRITE_TAC[c983fmc_input; ldisj] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: Input.reframe_left *)
let C983FMCE_INPUT_REFRAME_LEFT = prove
 (`forall cW sW uW vW aW cK sK uK vK aK cR sR uR vR aR.
     c983fmc_input cW sW uW vW aW cK sK uK vK aK /\ aR = aW /\
     (forall x y. linside cR sR uR vR aR x y <=> linside cW sW uW vW aW x y)
     ==> c983fmc_input cR sR uR vR aR cK sK uK vK aK`,
  REWRITE_TAC[c983fmc_input; ldisj] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: nonnegative_singleton_impossible *)
let C983FMCE_NONNEGATIVE_SINGLETON_IMPOSSIBLE = prove
 (c983fmc_stmt (C983FMC_ORIENT @ ["&0 < cK"; "&0 <= sK"; "sK <= cK"]) "F",
  C983FMC_OPEN_TAC THEN C983FMC_USE C983FMC_ANGLE_WINDOW THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `sW / (&1 + cW)`] C983FMCM_POSITIVE_COMPARISONS) THEN
  (ANTS_TAC THENL
    [REPEAT CONJ_TAC THEN
     FIRST [FIRST_ASSUM ACCEPT_TAC;
            REWRITE_TAC[REAL_POW_2] THEN FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC REAL_DIV_RMUL THEN RASM_ARITH_TAC;
            RASM_ARITH_TAC];
     DISCH_TAC]) THEN
  MP_TAC(SPECL (C983FMC_K @ C983FMC_W) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM(ACCEPT_TAC o SYM)]; ALL_TAC] THEN
  let close th = MATCH_MP_TAC (SPECL (C983FMC_W @ C983FMC_K) th) THEN REPEAT CONJ_TAC THEN
                 FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC] in
  let unit_tac =
    REWRITE_TAC[REAL_POW_2] THEN
    UNDISCH_TAC `cK * cK + sK * sK = &1` THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
    CONV_TAC REAL_RING in
  let cone nx ny =
    MP_TAC(SPECL (C983FMC_W @ C983FMC_K @ [nx; ny]) C983FMC_SEPARATOR_CONE) THEN
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
     [close C983FMCP_SINGLETON_POSITIVE_U; cone (ng `cK:real`) (ng `sK:real`)];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [cone `--sK` `cK:real`; cone (ng `--sK`) (ng `cK:real`)];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [close C983FMCP_SINGLETON_POSITIVE_W; cone (ng `cW:real`) (ng `sW:real`)];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [cone `--sW` `cW:real`; cone (ng `--sW`) (ng `cW:real`)]]);;

let C983FMCE_R = [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`];;

(* Lean: positive_sector *)
let C983FMCE_POSITIVE_SECTOR = prove
 (c983fmc_stmt ["&0 < cW"; "&0 <= sW"; "sW <= cW"] "linside cW sW uW vW aW (&0) (&0)",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL C983FMC_K CLF_CANONICAL_FRAME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cR:real` (X_CHOOSE_THEN `sR:real` (X_CHOOSE_THEN `uR:real`
    (X_CHOOSE_THEN `vR:real` (X_CHOOSE_THEN `aR:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `c983fmc_input cW sW uW vW aW cR sR uR vR aR` ASSUME_TAC THENL
   [MATCH_MP_TAC C983FMCE_INPUT_REFRAME_RIGHT THEN MAP_EVERY EXISTS_TAC C983FMC_K THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sR` THENL
   [MATCH_MP_TAC (SPECL (C983FMC_W @ C983FMCE_R) C983FMCE_NONNEGATIVE_SINGLETON_IMPOSSIBLE) THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC];
    MATCH_MP_TAC (SPECL (C983FMC_W @ C983FMCE_R @ [`--sR`])
      C983FMCN_NONPOSITIVE_SINGLETON_IMPOSSIBLE) THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC]]);;

let C983FMCE_WV = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;
let c983fmce_same m =
  let x = `x:real` and y = `y:real` in
  list_mk_forall([x; y], mk_iff(list_mk_comb(`linside`, C983FMCE_WV @ [x; y]), c983ab_in m x y));;

(* Lean: nonpositive_original *)
let C983FMCE_NONPOSITIVE_ORIGINAL =
  let same = c983fmce_same 2304 in
  let hyps = [C983F4F_NP; C983F4F_IMG; `cW * cW + sW * sW = &1`; `&0 < aW`;
              `&0 < cW`; `sW <= &0`; `--sW <= cW`; `(aW:real) = l`; same] in
  prove
   (list_mk_forall(C983E_VARS @ C983FMCE_WV,
      mk_imp(list_mk_conj hyps, `linside cW sW uW vW aW (&2) (&2)`)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
    let hh = c983f4f_hh () in
    let tr = REWRITE_RULE[GSYM (ASSUME same)] in
    let south = tr (seed 7 `&33 / &20` `&33 / &20`) in
    let north = tr (seed 7 `&33 / &20` `&47 / &20`) in
    let lowMissing = tr (excl 2304 2 (seed 1 `&1` `&87 / &50`)) in
    let leftAux = MP (SPECL C983E_VARS C983AB_LEFT_AUX) hh in
    let highMissing = tr (excl 2304 4096 (CONJUNCT1 leftAux)) in
    let noF3 = MP (SPECL C983E_VARS C983MTE_MERGED_NO_F3) hh in
    let topMissing = tr (PROVE_HYP noF3 (c983sa_missing 3 7)) in
    let leftMarker = seed 8 `&457 / &500` `&2` in
    let dj = REWRITE_RULE[ldisj; GSYM (ASSUME same)]
               (MP (SPECL C983E_VARS (oo_apart C983E_F 2304 4096)) hh) in
    let facts = [unit 4096; pos; box 4096; south; north; lowMissing; highMissing; topMissing;
                 leftMarker; CONJUNCT2 leftAux] in
    MATCH_MP_TAC (SPECL (C983FMCE_WV @ c983ab_own 4096) MLN_POINT) THEN
    REPEAT CONJ_TAC THEN
    FIRST (map ACCEPT_TAC facts @
           [FIRST_ASSUM ACCEPT_TAC; REFL_TAC; REWRITE_TAC[ldisj] THEN ACCEPT_TAC dj;
            MP_TAC side THEN RASM_ARITH_TAC]));;

(* Lean: center_of_singleton_corner *)
let C983FMCE_CENTER_OF_SINGLETON_CORNER =
  let f4tm = c983f4f_mem 4 7 and corner = c983ab_in 2 `&1` `&1` in
  let trW = c983fmc_tr C983FMCE_WV and tr2 = c983fmc_tr (c983ab_own 2)
  and tr2304 = c983fmc_tr (c983ab_own 2304) in
  prove
   (c983sa_stmt [f4tm; corner] (c983ab_in 2304 `&2` `&2`),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
    MP_TAC(MP (SPECL (c983ab_own 2304) CLF_CANONICAL_FRAME) (CONJ (unit 2304) pos)) THEN
    DISCH_THEN(X_CHOOSE_THEN `cW:real` (X_CHOOSE_THEN `sW:real` (X_CHOOSE_THEN `uW:real`
      (X_CHOOSE_THEN `vW:real` (X_CHOOSE_THEN `aW:real` STRIP_ASSUME_TAC))))) THEN
    SUBGOAL_THEN `linside cW sW uW vW aW (&2) (&2)` MP_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    ASM_CASES_TAC `&0 <= sW` THENL
     [(let actual = MP (SPECL C983E_VARS C983FMC_ACTUAL_INPUT)
                     (end_itlist CONJ [ASSUME C983F4F_NP; ASSUME C983F4F_IMG; ASSUME f4tm; ASSUME corner]) in
      SUBGOAL_THEN (list_mk_comb(`c983fmc_input`, trW @ tr2)) ASSUME_TAC THENL
       [MATCH_MP_TAC (SPECL (tr2304 @ tr2 @ trW) C983FMCE_INPUT_REFRAME_LEFT) THEN
        REPEAT CONJ_TAC THENL
         [ACCEPT_TAC actual; ASM_REWRITE_TAC[];
          REWRITE_TAC[CCIP_INSIDE_TRANSLATED] THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MP_TAC(SPECL (trW @ tr2) C983FMCE_POSITIVE_SECTOR) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN
        FIRST [ACCEPT_TAC (unit 2); ACCEPT_TAC pos; FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC];
        REWRITE_TAC[CCIP_INSIDE_TRANSLATED; REAL_ADD_RID]]);
      MATCH_MP_TAC (SPECL (C983E_VARS @ C983FMCE_WV) C983FMCE_NONPOSITIVE_ORIGINAL) THEN
      REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC]]);;
