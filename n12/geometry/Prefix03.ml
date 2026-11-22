(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Prefix03.lean                       *)
(* (S12Completion.C981.Coverage.prefix03, step03).  StepCheck is pc_stepcheck *)
(* (PrefixCoverage.ml), its decide proof the producer c981cov_step_check      *)
(* (Prefix01.ml).  Tag C981CP03_ / c981cov_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/Prefix01.ml";;
needs "n12/geometry/Prefix02.ml";;

(* Lean: prefix03 *)
let c981cov_prefix03 = new_definition
 `c981cov_prefix03 : ((num->bool)list)list =
   [[{2, 12}; {0, 10}; {1, 11}];
    [{2, 12}; {0, 10}; {1, 11, 13}];
    [{2, 12}; {0, 10}; {1, 3, 11}]]`;;

(* Lean: step03 *)
let C981CP03_STEP03 = c981cov_step_check c981cov_prefix02 c981cov_allowed8 c981cov_prefix03;;
