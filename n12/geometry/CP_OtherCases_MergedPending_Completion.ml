(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/Completion.lean      *)
(* (namespace N12Compact.MergedPending).  Original C683 and C867 contracts:  *)
(* the negative merged square H (owner 3072) meets the actual top square     *)
(* (owner 32768) in both angle ranges.  (Lean header: "Source only; not      *)
(* compiled".)  Conventions of NegativeUpperOutward.ml; upper_merged_        *)
(* impossible is an OCaml list over MPF_FAMILIES keeping 3072 IN family k    *)
(* (vacuous for c700).  C868.UpperNegativeCap.Data / impossible:             *)
(* c868cg_data / C868CG_IMPOSSIBLE; ClosedFrames.positive_frame:             *)
(* CLF_POSITIVE_FRAME.  Rows: 683 is row 364, 867 is row 454.  Tag MPCO_.    *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_NegativeUpperOutward.ml";;
needs "n12/geometry/UpperNegativeCapGeometry.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: upper_merged_impossible *)
let MPCO_UPPER_MERGED_IMPOSSIBLE = mpnuo_case
  (fun fam -> mpso_stmt fam [] `false`)
  (fun fam ->
    let i = index fam MPF_FAMILIES in
    let reach = CONJUNCT2 (mpwr_inst fam (el i MPWR_TOP_REACH)) in
    let far = MP (SPEC `&6 / &5` reach) (EQT_ELIM (REAL_RAT_REDUCE_CONV `&6 / &5 <= &6 / &5 /\ &6 / &5 <= &87 / &50`)) in
    let ap = REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam 3072 32768)) in
    let use th = MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) (el i th)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC in
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL MPWR_VARS (el i MPUN_UPPER_NEGATIVE_FRAME)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `cH:real` (X_CHOOSE_THEN `sH:real` (X_CHOOSE_THEN `uH:real`
      (X_CHOOSE_THEN `vH:real` (X_CHOOSE_THEN `aH:real` STRIP_ASSUME_TAC))))) THEN
    MPNUO_SUBST_TAC `aH:real` THEN
    SUBGOAL_THEN `c977cc_normal cH (--sH)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN
      REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
      ALL_TAC] THEN
    use MPNUA_UPPER_NEGATIVE_INPUT THEN use MPNUO_UPPER_NEAR_LOWER THEN
    use MPNUO_UPPER_TOP_CAP THEN use MPNUO_UPPER_SOUTHEAST_CAPS THEN
    SUBGOAL_THEN `c868cg_data cH sH (uH - (cH * &2 + sH * &2)) (vH - (--sH * &2 + cH * &2)) l`
      ASSUME_TAC THENL [REWRITE_TAC[c868cg_data] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* the actual top square in a positive frame *)
    MP_TAC(SPECL (mpwr_tuple 32768) CLF_POSITIVE_FRAME) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ACCEPT_TAC (mpuc_fix fam (mpse_unit fam 32768));
                                    ACCEPT_TAC (mpuc_fix fam (mpse_pos fam))]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `cT:real` (X_CHOOSE_THEN `sT:real` (X_CHOOSE_THEN `uT:real`
      (X_CHOOSE_THEN `vT:real` (X_CHOOSE_THEN `aT:real` STRIP_ASSUME_TAC))))) THEN
    MPNUO_SUBST_TAC `aT:real` THEN
    MATCH_MP_TAC (SPECL (MPNUO_HTL @ [`cT:real`; `sT:real`; `uT - (cT * &2 + sT * &2)`;
                                      `vT - (--sT * &2 + cT * &2)`; `l:real`]) C868CG_IMPOSSIBLE) THEN
    REWRITE_TAC[ldisj] THEN C868UI_TRANSLATE_TAC THEN
    mpnuo_facts fam [mpse_side fam; mpse_pos fam; far; mpwr_seed fam 32768 (`&2`, `&1543 / &500`)] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     (REPEAT GEN_TAC THEN ACCEPT_TAC (mpuc_fix fam (SPECL [`&2 + x`; `&2 + y`] ap)))));;

let mpco_family_excluded i =
  let fam = el i MPF_FAMILIES in
  prove(mk_comb(`excl_fam`, fam),
    REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (SPEC_ALL (el i MPCO_UPPER_MERGED_IMPOSSIBLE)) THEN
    ASM_REWRITE_TAC[in_fam 3072 fam]);;

(* Lean: family683_excluded *)
let MPCO_FAMILY683_EXCLUDED = mpco_family_excluded 0;;

(* Lean: family867_excluded *)
let MPCO_FAMILY867_EXCLUDED = mpco_family_excluded 2;;

(* Lean: lookup683 / lookup867 (private) *)
let MPCO_LOOKUP683 = ri_lookup 364 `mpf_family_c683`;;
let MPCO_LOOKUP867 = ri_lookup 454 `mpf_family_c867`;;

(* Lean: row683_family *)
let MPCO_ROW683_FAMILY = ri_family_at 364 `mpf_family_c683`;;

(* Lean: row867_family *)
let MPCO_ROW867_FAMILY = ri_family_at 454 `mpf_family_c867`;;

(* Lean: case683_excluded *)
let MPCO_CASE683_EXCLUDED = MP (ri_excludes_case 364 `mpf_family_c683`) MPCO_FAMILY683_EXCLUDED;;

(* Lean: case867_excluded *)
let MPCO_CASE867_EXCLUDED = MP (ri_excludes_case 454 `mpf_family_c867`) MPCO_FAMILY867_EXCLUDED;;

(* assembly rows *)
let MPCO_EXCLUDED_ROW683 = ri_excluded_row 364 MPCO_CASE683_EXCLUDED;;
let MPCO_EXCLUDED_ROW867 = ri_excluded_row 454 MPCO_CASE867_EXCLUDED;;
