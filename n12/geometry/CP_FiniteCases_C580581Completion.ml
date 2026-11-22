(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C580581Completion.lean             *)
(* (N12Compact.FiniteCases.C580581Completion).  Whole original C580/C581     *)
(* source composition: the shared entrance (C580TE_ENTRANCE.(v), owners 512, *)
(* 1024, 16384 with their disjointness) feeds the three-square contradiction *)
(* C983NTE_IMPOSSIBLE.  family v = C580E_FAM.(v); `family_impossible v` is   *)
(* the array FC580C_FAMILY_IMPOSSIBLE.(v).  RowIdentity.rowAt 321 / 322 are  *)
(* the HOL rows 321 / 322 (ri_excludes_case_iff checks id and family).      *)
(* Tag FC580C_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C580581TripleEntrance.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeTripleEnd.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: family_impossible *)
let FC580C_FAMILY_IMPOSSIBLE = Array.init 2 (fun v ->
  let sq = map (fun n -> mk_var(n, `:real`))
    ["cE"; "sE"; "uE"; "vE"; "aE"; "cN"; "sN"; "uN"; "vN"; "aN";
     "cR"; "sR"; "uR"; "vR"; "aR"] in
  prove(fc580ce_stmt v `false`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(fc580ce_inst v C580TE_ENTRANCE.(v)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC sq THEN STRIP_TAC THEN
    MATCH_MP_TAC(SPECL sq C983NTE_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]));;

(* Lean: row580, excludes580 *)
let FC580C_EXCLUDES580 = prove
 (`excl_case 580`,
  REWRITE_TAC[ri_excludes_case_iff 321 `c580e_family0`; excl_fam] THEN
  MESON_TAC[FC580C_FAMILY_IMPOSSIBLE.(0)]);;

(* Lean: row581, excludes581 *)
let FC580C_EXCLUDES581 = prove
 (`excl_case 581`,
  REWRITE_TAC[ri_excludes_case_iff 322 `c580e_family1`; excl_fam] THEN
  MESON_TAC[FC580C_FAMILY_IMPOSSIBLE.(1)]);;

(* the rows of cases 580 / 581 for the assembly *)
let FC580C_EXCLUDED_ROW580 = ri_excluded_row 321 FC580C_EXCLUDES580;;
let FC580C_EXCLUDED_ROW581 = ri_excluded_row 322 FC580C_EXCLUDES581;;
