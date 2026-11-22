(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Prefix00.lean                       *)
(* (S12Completion.C981.Coverage.prefix00): the initial (one empty front)      *)
(* prefix of the C981 prefix-coverage chain (PrefixCoverage.ml).  Lean lists  *)
(* of Finset Nat are HOL lists of num->bool.  Tag c981cov_ (as AllowedData).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/PrefixCoverage.ml";;
needs "n12/geometry/AllowedData.ml";;

(* Lean: prefix00 *)
let c981cov_prefix00 = new_definition
 `c981cov_prefix00 : ((num->bool)list)list = [[]]`;;
