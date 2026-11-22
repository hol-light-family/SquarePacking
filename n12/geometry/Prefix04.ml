(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Prefix04.lean                       *)
(* (S12Completion.C981.Coverage.prefix04, step04).  StepCheck is pc_stepcheck *)
(* (PrefixCoverage.ml), its decide proof the producer c981cov_step_check      *)
(* (Prefix01.ml).  Tag C981CP04_ / c981cov_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/Prefix01.ml";;
needs "n12/geometry/Prefix03.ml";;

(* Lean: prefix04 *)
let c981cov_prefix04 = new_definition
 `c981cov_prefix04 : ((num->bool)list)list =
   [[{2, 12}; {0, 10}; {1, 11}; {6, 15}];
    [{2, 12}; {0, 10}; {1, 11}; {6, 15, 18}];
    [{2, 12}; {0, 10}; {1, 11}; {4, 6, 15}];
    [{2, 12}; {0, 10}; {1, 11, 13}; {6, 15}];
    [{2, 12}; {0, 10}; {1, 11, 13}; {6, 15, 18}];
    [{2, 12}; {0, 10}; {1, 11, 13}; {4, 6, 15}];
    [{2, 12}; {0, 10}; {1, 3, 11}; {6, 15}];
    [{2, 12}; {0, 10}; {1, 3, 11}; {6, 15, 18}];
    [{2, 12}; {0, 10}; {1, 3, 11}; {4, 6, 15}]]`;;

(* Lean: step04 *)
let C981CP04_STEP04 = c981cov_step_check c981cov_prefix03 c981cov_allowed9 c981cov_prefix04;;
