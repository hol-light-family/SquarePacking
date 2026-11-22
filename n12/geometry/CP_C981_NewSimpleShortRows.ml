(* ========================================================================= *)
(* Port of Compact/Completion/C981/NewSimpleShortRows.lean                    *)
(* (N12Compact.C981CompletionNewSimpleShortRows).  The common-cycle geometry *)
(* reused for five more original rows: 54, 56, 58, 109 through the          *)
(* transposed adapter of Common107 (c981c107_excludes) and 73 directly       *)
(* through CommonRows (c981cr_excludes).  The Lean `decide +kernel` checks   *)
(* transposed_checked / checked73 are the producer runs (they fail unless   *)
(* every Check point/placement holds).  Tag C981NSSR_.                       *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_Common107.ml";;
needs "n12/geometry/CP_C981_CommonRows.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;

(* Lean: transposedIds *)
let c981nssr_transposed_ids = new_definition
 `c981nssr_transposed_ids = [54; 56; 58; 109]`;;

(* Lean: transposed_checked (Check v, via excludes v checked) *)
let C981NSSR_TRANSPOSED_CHECKED =
  map (fun i -> c981br_rep_excluded i c981c107_excludes) [54; 56; 58; 109];;

(* Lean: checked73 *)
let C981NSSR_CHECKED73 = c981br_rep_excluded 73 c981cr_excludes;;

(* Lean: coveredIds *)
let c981nssr_covered_ids = new_definition
 `c981nssr_covered_ids = [54; 56; 58; 73; 109]`;;

(* Lean: covered_excluded *)
let C981NSSR_COVERED_EXCLUDED =
  REWRITE_RULE[GSYM c981nssr_covered_ids]
    (c981br_covered [54; 56; 58; 73; 109] (C981NSSR_CHECKED73 :: C981NSSR_TRANSPOSED_CHECKED));;
