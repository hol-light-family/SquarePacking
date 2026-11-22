(* ========================================================================= *)
(* Phase 2: Compact/Bridge/TransformedOwnerBudget.lean.                      *)
(*   tob_transformed_singleton fam mask k sk (sw,rx,ry) n perm allowed       *)
(*   = Lean HalfDomain.ofTransformedSingletonSpec family mask k sourceKind t *)
(*     _ singleSpec_n _ hkind hlo hhi _ hmask perm hp allowed hallowed       *)
(*     hcount hne :   |- hdom fam mask k allowed                            *)
(* The side conditions are checked (spec kind sk, lower = upper = 1, mask    *)
(* action, the points permutation hp, the one-point budget, hallowed); the  *)
(* source local queries are re-proved for the image square.                 *)
(* Lean reflectXF, turnFG: RO_REFLECTXF, TBF_TURNFG.                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_TransposeOwnerDomain.ml";;

let TBF_TURNFG = [4;7;1;9;3;6;0;8;2;5];;

(* Lean: HalfDomain.ofTransformedSingletonSpec *)
let tob_transformed_singleton fam mask k sk trf n perm allowed =
  let (_, _, _, lo, hi, _) = pk_single_row n in
  if lo <> 1 || hi <> 1 then failwith "tob: spec bounds are not 1" else
  if pk_num (pklow_thm mask k) <> 1 || pk_num (pkup_thm fam mask k) <> 1 then
    failwith "tob: the budget is not exactly one point" else
  hdom_cache (tod_transported fam mask n trf sk k perm) allowed;;
