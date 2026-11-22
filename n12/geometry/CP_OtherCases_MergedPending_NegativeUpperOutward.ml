(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/NegativeUpperOutward *)
(* .lean (namespace N12Compact.MergedPending).  The outward top-marker       *)
(* reduction of C868 transferred to C683 and C867 with literal owners.       *)
(* Conventions of NegativeUpperActual.ml: per-case theorems are OCaml lists  *)
(* over MPF_FAMILIES (c683, c700, c867), each keeping the hypothesis         *)
(* 3072 IN family k (vacuous for c700); the OpenSquare H is cH sH uH vH aH   *)
(* with its invariants; H.translated 2 2 is                                  *)
(* (cH, sH, uH - (cH * &2 + sH * &2), vH - (--sH * &2 + cH * &2), aH).       *)
(* C868.UpperNegativeNear.lower_v / top_right_faces / top_cap_tilt:          *)
(* C868NR_LOWER_V / C868NR_TOP_RIGHT_FACES / C868NR_TOP_CAP_TILT;            *)
(* C868.UpperNegativeOutward.Faces / faces_original / top_lower_impossible:  *)
(* c868op_faces / C868OP_FACES_ORIGINAL / C868OE_TOP_LOWER_IMPOSSIBLE;       *)
(* C868.UpperNegativeCap.sharp_upper / lower_tilt / near_upper / span:       *)
(* C868CF_ lemmas; NegativeUpperFaces.top_marker_faces:                      *)
(* OCMPNUF_TOP_MARKER_FACES.  southeast_member (private) is in_fam.          *)
(* Tag MPNUO_.                                                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_SoutheastOutward.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_NegativeUpperActual.ml";;
needs "n12/geometry/UpperNegativeCapFaces.ml";;
needs "n12/geometry/UpperNegativeOutwardProfile.ml";;
needs "n12/geometry/UpperNegativeNear.ml";;

let MPNUO_HT = [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`; `vH - (--sH * &2 + cH * &2)`; `aH:real`];;
let MPNUO_HTL = [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`; `vH - (--sH * &2 + cH * &2)`; `l:real`];;
let MPNUO_BTL = [`cB:real`; `sB:real`; `uB - (cB * &2 + sB * &2)`; `vB - (--sB * &2 + cB * &2)`; `l:real`];;
let MPNUO_B = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

let MPNUO_HYPS_NOSHAPE = mpuc_sqhyps MPUN_H @ [`c977cc_normal cH (--sH)`; mpuc_equiv MPUN_H 3072 false];;
let MPNUO_HYPS_SHAPE = mpnua_hyps 3072 false;;

(* per case, vacuous for c700 *)
let mpnuo_case stmt tac = map (fun fam ->
  let tm = stmt fam in
  if rhs (concl (in_fam_conv 3072 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 3072 fam]) else
  prove (tm, tac fam)) MPF_FAMILIES;;

let mpnuo_facts fam ths = MAP_EVERY (fun th -> ASSUME_TAC (mpuc_fix fam (mpcp_norm th))) ths;;
let mpnuo_marks fam =
  CONJUNCTS (mpus_inst_member fam 3072 (el (index fam MPF_FAMILIES) MPF_UPPER_MERGED_MARKERS));;
let mpnuo_apart fam = REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam 3072 512));;
let MPNUO_CLOSE_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC ORELSE (CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC));;
let MPNUO_SUBST_TAC v =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = mk_eq(v, `l:real`)));;

(* Lean: upper_near_lower *)
let MPNUO_UPPER_NEAR_LOWER_BODY = `--(&1 / &20) * (cH - sH) <= vH - (--sH * &2 + cH * &2)`;;
let MPNUO_UPPER_NEAR_LOWER = mpnuo_case
  (fun fam -> mpnua_stmt fam true MPNUO_HYPS_NOSHAPE MPNUO_UPPER_NEAR_LOWER_BODY)
  (fun fam ->
    let marks = mpnuo_marks fam in
    let points = CONJUNCTS (mpwr_inst fam (el (index fam MPF_FAMILIES) MPCP_SOUTHWEST_POINTS)) in
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (SPECL MPNUO_HT C868NR_LOWER_V) THEN C868UI_TRANSLATE_TAC THEN
    mpnuo_facts fam [el 0 marks; el 1 marks; mpcp_excl fam 3072 256 (el 2 points)] THEN
    MPNUO_CLOSE_TAC);;

(* Lean: upper_top_right_faces *)
let MPNUO_UPPER_TOP_RIGHT_FACES_BODY =
  `&13 / &50 * cH + sH <= uH - (cH * &2 + sH * &2) \/
   (vH - (--sH * &2 + cH * &2)) + aH <= cH - &13 / &50 * sH`;;
let MPNUO_UPPER_TOP_RIGHT_FACES = mpnuo_case
  (fun fam -> mpnua_stmt fam true MPNUO_HYPS_NOSHAPE MPNUO_UPPER_TOP_RIGHT_FACES_BODY)
  (fun fam ->
    let marks = mpnuo_marks fam in
    let top = mpwr_bar (el 2 (mpcp_walls fam)) `&113 / &50` in
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (SPECL MPNUO_HT C868NR_TOP_RIGHT_FACES) THEN C868UI_TRANSLATE_TAC THEN
    mpnuo_facts fam [el 1 marks; mpcp_excl fam 3072 16 top] THEN
    MPNUO_CLOSE_TAC);;

(* Lean: southeast_full_outward_profile *)
let MPNUO_PROFILE_BODY =
  list_mk_exists(MPNUO_B, list_mk_conj (mpuc_sqhyps MPNUO_B @ [`aB:real = l`; mpuc_equiv MPNUO_B 512 false;
    `c868op_faces cB sB (uB - (cB * &2 + sB * &2)) (vB - (--sB * &2 + cB * &2)) aB`]));;
let MPNUO_SOUTHEAST_FULL_OUTWARD_PROFILE = mpnuo_case
  (fun fam -> mpso_stmt fam [] MPNUO_PROFILE_BODY)
  (fun fam ->
    let i = index fam MPF_FAMILIES in
    let corner p = mpwr_excl fam 512 12 (mpwr_seed fam 12 p) in
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL MPWR_VARS (el i MPSO_SOUTHEAST_OUTWARD_FRAME_UNCONDITIONAL)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `cB:real` (X_CHOOSE_THEN `sB:real` (X_CHOOSE_THEN `uB:real`
      (X_CHOOSE_THEN `vB:real` (X_CHOOSE_THEN `aB:real` STRIP_ASSUME_TAC))))) THEN
    MPNUO_SUBST_TAC `aB:real` THEN
    MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`] C868OP_FACES_ORIGINAL) THEN
    C868UI_IFF_TAC THEN
    SUBGOAL_THEN `c977cc_normal cB (--sB)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN
      REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
      ALL_TAC] THEN
    mpnuo_facts fam
     [mpse_side fam; mpwr_seed fam 512 (`&47 / &20`, `&33 / &20`); mpse_f8 fam; mpso_miss fam;
      mpwr_missing fam 512 14; corner (`&3`, `&1`); corner (`&1543 / &500`, `&1`)] THEN
    ASSUME_TAC (mpuc_fix fam (mpse_bottom fam)) THEN
    MPNUO_CLOSE_TAC);;

(* Lean: upper_top_cap *)
let MPNUO_UPPER_TOP_CAP_BODY = `(vH - (--sH * &2 + cH * &2)) + aH <= &543 / &500 * cH`;;
let MPNUO_UPPER_TOP_CAP = mpnuo_case
  (fun fam -> mpnua_stmt fam true MPNUO_HYPS_SHAPE MPNUO_UPPER_TOP_CAP_BODY)
  (fun fam ->
    let i = index fam MPF_FAMILIES in
    let pts = mpus_inst_member fam 3072 (el i MPSO_SOUTHEAST_OUTWARD_POINTS_UNCONDITIONAL) in
    REPEAT GEN_TAC THEN STRIP_TAC THEN MPNUO_SUBST_TAC `aH:real` THEN
    MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) (el i MPNUA_UPPER_NEGATIVE_INPUT)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC (SPECL MPNUO_HTL OCMPNUF_TOP_MARKER_FACES) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MP_TAC(SPECL MPWR_VARS (el i MPNUO_SOUTHEAST_FULL_OUTWARD_PROFILE)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `cB:real` (X_CHOOSE_THEN `sB:real` (X_CHOOSE_THEN `uB:real`
      (X_CHOOSE_THEN `vB:real` (X_CHOOSE_THEN `aB:real` STRIP_ASSUME_TAC))))) THEN
    MPNUO_SUBST_TAC `aB:real` THEN
    MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) (el i MPNUO_UPPER_NEAR_LOWER)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) (el i MPNUO_UPPER_TOP_RIGHT_FACES)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC (TAUT `false ==> p`) THEN
    MATCH_MP_TAC (SPECL (MPNUO_HTL @ MPNUO_BTL) C868OE_TOP_LOWER_IMPOSSIBLE) THEN
    REWRITE_TAC[ldisj] THEN C868UI_TRANSLATE_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE REAL_RAT_REDUCE_CONV) THEN
    mpnuo_facts fam [mpwr_seed fam 512 (`&47 / &20`, `&33 / &20`); CONJUNCT2 pts] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC ORELSE
     (REPEAT GEN_TAC THEN ACCEPT_TAC (mpuc_fix fam (SPECL [`&2 + x`; `&2 + y`] (mpnuo_apart fam))))));;

(* Lean: upper_shallow *)
let MPNUO_UPPER_SHALLOW = mpnuo_case
  (fun fam -> mpnua_stmt fam true MPNUO_HYPS_SHAPE `--(&3) * sH < &2 * cH`)
  (fun fam ->
    let i = index fam MPF_FAMILIES in
    REPEAT GEN_TAC THEN STRIP_TAC THEN MPNUO_SUBST_TAC `aH:real` THEN
    MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) (el i MPNUO_UPPER_NEAR_LOWER)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) (el i MPNUO_UPPER_TOP_CAP)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC (SPECL MPNUO_HTL C868NR_TOP_CAP_TILT) THEN
    mpnuo_facts fam [mpse_side fam] THEN MPNUO_CLOSE_TAC);;

(* Lean: upper_southeast_caps *)
let MPNUO_UPPER_SOUTHEAST_CAPS_BODY =
  `(uH - (cH * &2 + sH * &2)) + aH <= &21 / &40 * cH + &1 / &8 * sH /\
   (uH - (cH * &2 + sH * &2)) + aH <= &23 / &50 * cH + &1 / &100 * sH /\
   &1 < &18 / &25 * cH - &99 / &100 * sH`;;
let MPNUO_UPPER_SOUTHEAST_CAPS = mpnuo_case
  (fun fam -> mpnua_stmt fam true MPNUO_HYPS_SHAPE MPNUO_UPPER_SOUTHEAST_CAPS_BODY)
  (fun fam ->
    let i = index fam MPF_FAMILIES in
    let pts = mpus_inst_member fam 3072 (el i MPSO_SOUTHEAST_OUTWARD_POINTS_UNCONDITIONAL) in
    REPEAT GEN_TAC THEN STRIP_TAC THEN MPNUO_SUBST_TAC `aH:real` THEN
    MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) (el i MPNUA_UPPER_NEGATIVE_INPUT)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) (el i MPNUO_UPPER_TOP_CAP)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `~linside cH sH (uH - (cH * &2 + sH * &2)) (vH - (--sH * &2 + cH * &2)) l
               (&21 / &40) (&1 / &8) /\
      ~linside cH sH (uH - (cH * &2 + sH * &2)) (vH - (--sH * &2 + cH * &2)) l
               (&23 / &50) (&1 / &100)` STRIP_ASSUME_TAC THENL
     [C868UI_TRANSLATE_TAC THEN
      mpnuo_facts fam [mpso_excl fam 3072 512 (CONJUNCT2 pts); mpso_excl fam 3072 512 (CONJUNCT1 pts)] THEN
      MPNUO_CLOSE_TAC;
      ALL_TAC] THEN
    C868UI_USE MPNUO_HTL C868CF_SHARP_UPPER THEN
    C868UI_USE MPNUO_HTL C868CF_LOWER_TILT THEN
    C868UI_USE MPNUO_HTL C868CF_NEAR_UPPER THEN
    C868UI_USE MPNUO_HTL C868CF_SPAN THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;
