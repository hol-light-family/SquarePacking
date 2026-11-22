(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualTwoFifths.lean                 *)
(* (N12Compact.C1092MPPMActualTwoFifths).  The actual MPPM right-near        *)
(* one-omission ending: every square in the common chart                     *)
(* (x,y) |-> (2+y,2+x); W/N/E/R are original Q5/Q6/Q7/Q11.                   *)
(* (Lean header: "Source only, uncompiled".)                                 *)
(* Conventions and forward toolkit of CP_C1092_MPPMOmissionCenter.ml         *)
(* (c1092moc_*; owners p i at mask EL i c1092wc_code, side l; WallContext p  *)
(* mppm is C1092MPPE_CTX, omitted is C1092MPPE_OMIT, near is C1092MARN_NEAR).*)
(* The private side_gt / side_same / mark are OO_SIDE / l = l / oo_seed      *)
(* markers (c1092moc_side, c1092moc_seed).                                   *)
(* MPPMUpperSign.PositiveActual p N = c1092mpus_pos .. cN sN uN vN aN,       *)
(* exists_positive C1092MPUS_EXISTS_POSITIVE; MPPMActualProfiles.            *)
(* southeast_profile / northeast_core / right_profile C1092MPAP_* (E's       *)
(* SoutheastActual = c1092mpap_actual); MPPMNorthwestActualSign.             *)
(* exists_positive C1092MPNWAS_EXISTS_POSITIVE (PositiveActual =             *)
(* c1092mpnwas_pos); omitted_bottom_inward / omitted_bottom_bar              *)
(* C1092MPPE_OMITTED_BOTTOM_INWARD / _BAR; bottom_center                     *)
(* C1092MOC_BOTTOM_CENTER; MPPMPointCore.diagonal C1092MPC_DIAGONAL;         *)
(* TwoFifthsEntranceNorthwestGeometry southeast_height /                     *)
(* positive_northwest_height / _faces / _left_face C1092MTFNW_*;             *)
(* MMMPUpperThird.upper_third C1092MUT_UPPER_THIRD; NortheastCore.complete   *)
(* C1092MTFEN_NORTHEASTCORE_COMPLETE; C1092TwoFifths.impossible              *)
(* C1092TFEN_IMPOSSIBLE (input C1092TF_input); MPPMActualOneOmission.        *)
(* impossible_of_top_g4_omission C1092MPAOO_IMPOSSIBLE_OF_TOP_G4_OMISSION.   *)
(* (pullSwap (owners p 11)).translated 2 2 is c1092mpap_swtr 11.             *)
(* Tag C1092MPATF_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualProfiles.ml";;
needs "n12/geometry/CP_C1092_MPPMNorthwestActualSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceNorthwestGeometry.ml";;
needs "n12/geometry/CP_C1092_MMMP_UpperThird.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsEnding.ml";;
needs "n12/geometry/CP_C1092_MPPMActualOneOmission.ml";;

let C1092MPATF_EV = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
and C1092MPATF_WV = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
and C1092MPATF_NV = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`];;

(* prove a conjunction of assumptions *)
let rec c1092mpatf_build tm =
  if is_conj tm then CONJ (c1092mpatf_build (lhand tm)) (c1092mpatf_build (rand tm))
  else ASSUME tm;;
let c1092mpatf_use th args =
  let t = SPECL args th in MP t (c1092mpatf_build (lhand (concl t)));;

(* facts of a structure predicate: unfold, literal masks, split *)
let c1092mpatf_facts def tm =
  CONJUNCTS (CONV_RULE C1092MOC_CODE_CONV (REWRITE_RULE[def] (ASSUME tm)));;

(* ldisj of two charts from their actual equivalences and the original apartness *)
let c1092mpatf_disj eqs apart tm =
  let eq = (REWRITE_CONV[ldisj] THENC GEN_REWRITE_CONV ONCE_DEPTH_CONV eqs) tm in
  let r = rhs (concl eq) in
  EQ_MP (SYM eq) (MP (prove(mk_imp(concl apart, r),
    DISCH_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[])) apart);;

let c1092mpatf_bot x =
  let bbar = c1092moc_use C1092MPPE_OMITTED_BOTTOM_BAR in
  let rr tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm) in
  let th = SPEC x bbar in MP (MP th (rr (lhand (concl th)))) (rr (lhand (rand (concl th))));;

(* the forward proof of upper_third, all facts assumed *)
let c1092mpatf_upper () =
  let ev = C1092MPATF_EV and wv = C1092MPATF_WV and nv = C1092MPATF_NV in
  let _, npos, [nunit; npos0; nside; ninside; nnormal; npositive] = c1092mpaoo_n () in
  let [eside; einside; enormal; epos] =
    c1092mpatf_facts c1092mpap_actual (list_mk_comb(`c1092mpap_actual`, C1092MPPE_V @ ev)) in
  let [wside; winside; wnormal; wpos] =
    c1092mpatf_facts c1092mpnwas_pos (list_mk_comb(`c1092mpnwas_pos`, C1092MPPE_V @ wv)) in
  let eunit = ASSUME `cE * cE + sE * sE = &1` and eapos = ASSUME `&0 < aE` in
  let ese = ASSUME `C1092TF_southeast cE sE uE vE aE` in
  let ecap = ASSUME `uE + aE <= cE - (&13 / &50) * sE` in
  let wunit = ASSUME `cW * cW + sW * sW = &1` and wapos = ASSUME `&0 < aW` in
  let pt = c1092mtfes_pt winside and npt = c1092mtfes_npt winside in
  let pair = c1092moc_use C1092MPPE_OMITTED_BOTTOM_INWARD in
  let origin = pt `&0` `&0` (c1092moc_use C1092MOC_BOTTOM_CENTER) in
  let left = pt `--(&13 / &50)` `&0` (CONJUNCT1 pair) in
  let north = pt `&0` `&13 / &50` (CONJUNCT2 pair) in
  let diagonal = pt `--(&1 / &2)` `&1 / &2` (CONJUNCT1 (c1092moc_use C1092MPC_DIAGONAL)) in
  let marker = pt `--(&7 / &20)` `&7 / &20` (c1092moc_seed 5 (`&47 / &20`, `&33 / &20`)) in
  let missingSW = npt `--(&7 / &20)` `--(&7 / &20)`
      (c1092moc_excl 5 4 (c1092moc_seed 4 (`&33 / &20`, `&33 / &20`))) in
  let missingNE = npt `&7 / &20` `&7 / &20`
      (c1092moc_excl 5 6 (c1092moc_seed 6 (`&47 / &20`, `&47 / &20`))) in
  let missingLeft = npt `--(&1)` `&39 / &100` (c1092moc_excl 5 9 (c1092mpatf_bot `&239 / &100`)) in
  let missingFar = npt `--(&1)` `&2 / &5` (c1092moc_excl 5 9 (c1092mpatf_bot `&12 / &5`)) in
  let apartEW = c1092mpatf_disj [einside; winside] (c1092moc_apart 7 5)
    (list_mk_comb(`ldisj`, ev @ wv)) in
  let apartWN = c1092mpatf_disj [winside; ninside] (c1092moc_apart 5 6)
    (list_mk_comb(`ldisj`, wv @ nv)) in
  let seh = c1092moc_apply2 ALL_CONV (SPECL ev C1092MTFNW_SOUTHEAST_HEIGHT)
    [eunit; eapos; ese; ecap] [] in
  let height = c1092moc_apply2 ALL_CONV (SPECL (ev @ wv) C1092MTFNW_POSITIVE_NORTHWEST_HEIGHT)
    [eunit; eapos; wunit; wapos; ese; wnormal; seh; origin; left; north; apartEW]
    [eside; wside] in
  let sideW = c1092moc_arith [wside; c1092moc_side ()] `&1 < aW` in
  let angle = c1092moc_apply2 ALL_CONV (SPECL wv C1092MTFNW_POSITIVE_NORTHWEST_FACES)
    [wunit; wapos; sideW; wnormal; origin; diagonal; missingSW; missingNE; missingLeft] [] in
  let floor = c1092moc_apply2 ALL_CONV (SPECL wv C1092MTFNW_POSITIVE_NORTHWEST_LEFT_FACE)
    [wunit; wapos; wnormal; angle; height; origin; missingFar] [] in
  let core = c1092mpatf_use C1092MPAP_NORTHEAST_CORE (C1092MPPE_V @ nv) in
  c1092moc_apply2 ALL_CONV (SPECL (wv @ nv) C1092MUT_UPPER_THIRD)
    [wunit; wapos; nunit; npos0; sideW; wnormal; angle; origin; marker; floor; core; apartWN]
    [wside; nside; height];;

(* Lean: upper_third *)
let C1092MPATF_UPPER_THIRD = prove
 (parse_term (Printf.sprintf "!%s cN sN uN vN aN. %s /\\ c1092mpus_pos %s cN sN uN vN aN
      ==> &3 * sN < &1 + cN" C1092AE_P C1092MARN_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPATF_NV) C1092MPAP_SOUTHEAST_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cE:real` (X_CHOOSE_THEN `sE:real` (X_CHOOSE_THEN `uE:real`
    (X_CHOOSE_THEN `vE:real` (X_CHOOSE_THEN `aE:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPNWAS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cW:real` (X_CHOOSE_THEN `sW:real` (X_CHOOSE_THEN `uW:real`
    (X_CHOOSE_THEN `vW:real` (X_CHOOSE_THEN `aW:real` STRIP_ASSUME_TAC))))) THEN
  ACCEPT_TAC (c1092mpatf_upper ()));;

(* the forward proof of impossible_of_top_g4, all facts assumed *)
let c1092mpatf_top_g4 () =
  let ev = C1092MPATF_EV and nv = C1092MPATF_NV in
  let _, npos, [nunit; npos0; nside; ninside; nnormal; npositive] = c1092mpaoo_n () in
  let [eside; einside; enormal; epos] =
    c1092mpatf_facts c1092mpap_actual (list_mk_comb(`c1092mpap_actual`, C1092MPPE_V @ ev)) in
  let eunit = ASSUME `cE * cE + sE * sE = &1` and eapos = ASSUME `&0 < aE` in
  let ese = ASSUME `C1092TF_southeast cE sE uE vE aE` in
  let tR, eqR = c1092mpap_swtr 11 in
  let upper = c1092mpatf_use C1092MPATF_UPPER_THIRD (C1092MPPE_V @ nv) in
  let core = c1092mpatf_use C1092MPAP_NORTHEAST_CORE (C1092MPPE_V @ nv) in
  let northeast = MP (SPECL nv C1092MTFEN_NORTHEASTCORE_COMPLETE)
    (CONJ core (MATCH_MP REAL_LT_IMP_LE upper)) in
  let right = c1092mpatf_use C1092MPAP_RIGHT_PROFILE C1092MPPE_V in
  let apartER = c1092mpatf_disj [einside; eqR] (c1092moc_apart 7 11)
    (list_mk_comb(`ldisj`, ev @ tR)) in
  let apartNR = c1092mpatf_disj [ninside; eqR] (c1092moc_apart 6 11)
    (list_mk_comb(`ldisj`, nv @ tR)) in
  let input = c1092moc_apply2 ALL_CONV
    (snd (EQ_IMP_RULE (SPECL (ev @ nv @ tR) C1092TF_input)))
    [ese; northeast; right; apartER; apartNR] [eside; nside] in
  c1092moc_apply2 ALL_CONV (SPECL (ev @ nv @ tR) C1092TFEN_IMPOSSIBLE)
    [eunit; eapos; nunit; npos0; c1092moc_punit 11 tR; c1092moc_pos (); input] [];;

(* Lean: impossible_of_top_g4 *)
let C1092MPATF_IMPOSSIBLE_OF_TOP_G4 = prove
 (parse_term (Printf.sprintf "!%s. %s ==> F" C1092AE_P C1092MARN_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPUS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cN:real` (X_CHOOSE_THEN `sN:real` (X_CHOOSE_THEN `uN:real`
    (X_CHOOSE_THEN `vN:real` (X_CHOOSE_THEN `aN:real` ASSUME_TAC))))) THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPATF_NV) C1092MPAP_SOUTHEAST_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cE:real` (X_CHOOSE_THEN `sE:real` (X_CHOOSE_THEN `uE:real`
    (X_CHOOSE_THEN `vE:real` (X_CHOOSE_THEN `aE:real` STRIP_ASSUME_TAC))))) THEN
  ACCEPT_TAC (c1092mpatf_top_g4 ()));;

(* Lean: impossible *)
let C1092MPATF_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s. %s ==> F" C1092AE_P C1092MPRI_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC C1092MARN_NEAR_TM THENL
   [MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPATF_IMPOSSIBLE_OF_TOP_G4) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPAOO_IMPOSSIBLE_OF_TOP_G4_OMISSION) THEN
    ASM_REWRITE_TAC[]]);;
