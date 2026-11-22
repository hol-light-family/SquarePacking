(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedPending/C700Completion.lean   *)
(* (namespace N12Compact.MergedPending).  Complete original C700 exclusion:  *)
(* the distinct actual singletons 1 and 2 both contain (1,1) strictly.       *)
(* family .c700 is mpf_family_c700; ExcludesFamily / ExcludesCase are        *)
(* excl_fam / excl_case; rowAt 381 via ri_lookup / ri_family_at              *)
(* (RowIdentity.ml).  (Lean header: "This source has not been compiled".)    *)
(* Tag MPC700_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_C700FullCornerSingleton.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_C700LeftCornerSingleton.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: family700_excluded *)
let MPC700_FAMILY700_EXCLUDED = prove
 (`excl_fam mpf_family_c700`,
  REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  let fam = `mpf_family_c700` in
  let ap = REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam 1 2)) in
  MP_TAC(SPECL [`&1`; `&1`] ap) THEN
  REWRITE_TAC[mpwr_inst fam MPFCS_C700_BOTTOM_SINGLETON_CORNER;
              mpwr_inst fam MPLCS_C700_LEFT_SINGLETON_CORNER]);;

(* Lean: lookup700 (private) *)
let MPC700_LOOKUP700 = ri_lookup 381 `mpf_family_c700`;;

(* Lean: row700_family *)
let MPC700_ROW700_FAMILY = ri_family_at 381 `mpf_family_c700`;;

(* Lean: case700_excluded *)
let MPC700_CASE700_EXCLUDED = MP (ri_excludes_case 381 `mpf_family_c700`) MPC700_FAMILY700_EXCLUDED;;

let MPC700_EXCLUDED_ROW = ri_excluded_row 381 MPC700_CASE700_EXCLUDED;;
