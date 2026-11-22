(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Prefix02.lean                       *)
(* (S12Completion.C981.Coverage.prefix02, step02).  StepCheck is pc_stepcheck *)
(* (PrefixCoverage.ml), its decide proof the producer c981cov_step_check      *)
(* (Prefix01.ml).  Tag C981CP02_ / c981cov_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/Prefix01.ml";;

(* Lean: prefix02 *)
let c981cov_prefix02 = new_definition
 `c981cov_prefix02 : ((num->bool)list)list = [[{2, 12}; {0, 10}]]`;;

(* Lean: step02 *)
let C981CP02_STEP02 = c981cov_step_check c981cov_prefix01 c981cov_allowed1 c981cov_prefix02;;
