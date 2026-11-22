(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C974/ActualEnding.lean              *)
(* (namespace N12Compact.Completion.OtherCases.C974.OriginalData).  Both     *)
(* literal C974 missing-corner roots are discharged by the full raw          *)
(* three-square theorem C983.C974LocalEnding.impossible (C983LE_IMPOSSIBLE). *)
(* C983.C974LocalData.Input = c983ld_input over (q).translated 1 1 /         *)
(* (pullSwap q).translated 1 1 tuples (c983ld_tr / c983ld_sw).  owners p 0 / *)
(* 1 / 2 / 4 / 8 / 9 = owner 1 / 2 / 12 / 192 / 4096 / 8192 (EL i           *)
(* c974od_masks).  fixed = C974EG_FIXED (c974lo_fixed), seed = oo_seed,      *)
(* foreign = oo_excl, apart = oo_apart, box = OO_BOX, side = OO_SIDE,        *)
(* missing_zero / missing_one = C974OD_MISSING_ZERO / ONE, missing_northwest *)
(* = oo_missing 4096 11, bottom_origin / bottom_reach / southwest_south /    *)
(* southwest_west / southeast_lower = C974EG_*, left_origin / left_reach /   *)
(* top_halfpoint = C974LO_*.  Hypotheses hf / missing are curried as in Lean.*)
(* Added for the assembly (Lean: Completion.lean, row 505):                  *)
(* C974AE_EXCLUDES (excl_case 974) and C974AE_EXCLUDED_ROW.  Tag C974AE_.    *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C974_LeftOrigin.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LocalEnding.ml";;
needs "n12/geometry/RowIdentity.ml";;

let c974ae_stmt hyps body =
  list_mk_forall(C974LO_VARS, mk_imp(c974lo_hyp, itlist (curry mk_imp) hyps body));;

let c974ae_conj2 th missing = CONJUNCTS (MP (SPECL C974LO_VARS th) (CONJ c974lo_np (CONJ
  (CONJUNCT2 (ASSUME c974lo_hyp)) (ASSUME missing))));;

(* Lean: bottom_input *)
let C974AE_BOTTOM_INPUT =
  let missing = mk_neg (c974lo_own 1 `&1` `&1`) in
  let seeds = c974ae_conj2 C974OD_MISSING_ZERO missing in
  let sel = c974lo_inst C974EG_SOUTHEAST_LOWER in
  let facts = [C974LO_SIDE; c974lo_seed 1 (`&1`, `&457 / &500`); el 0 seeds; el 1 seeds;
               ASSUME missing; c974lo_inst C974EG_BOTTOM_ORIGIN;
               c974lo_fixed 8192 `&2` `&457 / &500`;
               CONJUNCT1 (c974lo_inst C974EG_BOTTOM_REACH);
               c974lo_excl 8192 512 (c974lo_fixed 512 `&47 / &20` `&33 / &20`);
               c974lo_excl 8192 256 (c974lo_inst C974EG_SOUTHWEST_SOUTH);
               c974lo_excl 8192 512 sel;
               c974lo_fixed 12 `&3` `&1`; c974lo_excl 12 512 sel;
               REWRITE_RULE[ldisj] (c974lo_apart 1 8192); REWRITE_RULE[ldisj] (c974lo_apart 1 12);
               REWRITE_RULE[ldisj] (c974lo_apart 8192 12)] in
  prove
   (c974ae_stmt [missing]
      (c983ld_concl (c983ld_tr (c974lo_tuple 1)) (c983ld_tr (c974lo_tuple 8192))
                    (c983ld_tr (c974lo_tuple 12))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    C983LD_CLOSE_TAC facts [REWRITE_RULE[lcont] (c974lo_box 1); REWRITE_RULE[lcont] (c974lo_box 12)]);;

(* Lean: left_input *)
let C974AE_LEFT_INPUT =
  let missing = mk_neg (c974lo_own 2 `&1` `&1`) in
  let seeds = c974ae_conj2 C974OD_MISSING_ONE missing in
  let top = c974lo_inst C974LO_TOP_HALFPOINT in
  let facts = [C974LO_SIDE; c974lo_seed 2 (`&457 / &500`, `&1`); el 0 seeds; el 1 seeds;
               ASSUME missing; c974lo_inst C974LO_LEFT_ORIGIN;
               c974lo_fixed 4096 `&457 / &500` `&2`;
               c974lo_inst C974LO_LEFT_REACH;
               c974lo_missing 4096;
               c974lo_excl 4096 256 (c974lo_inst C974EG_SOUTHWEST_WEST);
               c974lo_excl 4096 32768 top;
               c974lo_fixed 192 `&1` `&3`; c974lo_excl 192 32768 top;
               REWRITE_RULE[ldisj] (c974lo_apart 2 4096); REWRITE_RULE[ldisj] (c974lo_apart 2 192);
               REWRITE_RULE[ldisj] (c974lo_apart 4096 192)] in
  let tr t = c983ld_tr (c983ld_sw t) in
  prove
   (c974ae_stmt [missing]
      (c983ld_concl (tr (c974lo_tuple 2)) (tr (c974lo_tuple 4096)) (tr (c974lo_tuple 192))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    C983LD_CLOSE_TAC facts [REWRITE_RULE[lcont] (c974lo_box 2); REWRITE_RULE[lcont] (c974lo_box 192)]);;

(* the C983LE_IMPOSSIBLE side conditions for three owners *)
let C974AE_CLOSE tK tW tC ms inth =
  let units = map c974lo_unit ms in
  let pos = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) C974LO_SIDE in
  let th = SPECL (tK @ tW @ tC) C983LE_IMPOSSIBLE in
  let ant = lhand (concl th) in
  MP th (TAC_PROOF(([], ant),
    REPEAT CONJ_TAC THEN
    FIRST [ACCEPT_TAC pos; ACCEPT_TAC inth;
           MAP_EVERY MP_TAC units THEN REAL_ARITH_TAC]));;

(* Lean: impossible *)
let C974AE_IMPOSSIBLE =
  let first = c974lo_own 1 `&1` `&1` in
  let tr t = c983ld_tr (c983ld_sw t) in
  let left_case =
    let second =
      let d2 = SPECL [`&1`; `&1`] (REWRITE_RULE[ldisj] (c974lo_apart 2 1)) in
      let qa = lhand (rand (concl d2)) in
      NOT_INTRO (DISCH qa (MP (NOT_ELIM d2) (CONJ (ASSUME qa) (ASSUME first)))) in
    let inth = MP (c974lo_inst C974AE_LEFT_INPUT) second in
    C974AE_CLOSE (tr (c974lo_tuple 2)) (tr (c974lo_tuple 4096)) (tr (c974lo_tuple 192))
      [2; 4096; 192] inth in
  let bottom_case =
    let inth = MP (c974lo_inst C974AE_BOTTOM_INPUT) (ASSUME (mk_neg first)) in
    C974AE_CLOSE (c983ld_tr (c974lo_tuple 1)) (c983ld_tr (c974lo_tuple 8192))
      (c983ld_tr (c974lo_tuple 12)) [1; 8192; 12] inth in
  let th = DISJ_CASES (SPEC first EXCLUDED_MIDDLE) left_case bottom_case in
  prove(c974ae_stmt [] `false`, REPEAT GEN_TAC THEN DISCH_TAC THEN ACCEPT_TAC th);;

(* Lean (Completion.lean): case_excluded, via family_excluded at row 505 *)
let C974AE_EXCLUDES = prove
 (`excl_case 974`,
  REWRITE_TAC[ri_excludes_case_iff 505 `c974d_family`; excl_fam] THEN
  MESON_TAC[C974AE_IMPOSSIBLE]);;

(* for the assembly: |- EXCLUDED_ROW 505 *)
let C974AE_EXCLUDED_ROW = ri_excluded_row 505 C974AE_EXCLUDES;;
