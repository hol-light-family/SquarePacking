(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Prefix10.lean                       *)
(* (S12Completion.C981.Coverage.step10).  prefix10 is the Data table          *)
(* c981cov_prefix10 (CC_C981_Coverage_Data_Prefix10.ml, chunks of FinsetPool  *)
(* constants); it is first evaluated to a literal table                      *)
(* (C981CP10_PREFIX10_LITERAL), then StepCheck is proved by the producer      *)
(* c981cov_step_check (Prefix01.ml; Lean stepCheck_of_extensions_eq + rfl).   *)
(* Tag C981CP10_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Prefix01.ml";;
needs "n12/geometry/CC_C981_Coverage_Prefix09.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10.ml";;

(* |- c981cov_prefix10 = [literal table] *)
let C981CP10_PREFIX10_LITERAL =
  (REWR_CONV c981cov_prefix10 THENC
   REWRITE_CONV[c981cov_prefix10chunk000; c981cov_prefix10chunk001; c981cov_prefix10chunk002;
                c981cov_prefix10chunk003; c981cov_prefix10chunk004; c981cov_prefix10chunk005;
                c981cov_prefix10chunk006; c981cov_prefix10chunk007; c981cov_prefix10chunk008;
                c981cov_prefix10chunk009; c981cov_prefix10chunk010; c981cov_prefix10chunk011;
                c981cov_prefix10chunk012] THENC
   REWRITE_CONV C981CP09_POOL THENC c981cov_appchain_conv) `c981cov_prefix10`;;

(* Lean: step10  (prefix09 as the literal C981CP09_PREFIX09_LITERAL) *)
let C981CP10_STEP10 =
  c981cov_step_check C981CP09_PREFIX09_LITERAL c981cov_allowed5 C981CP10_PREFIX10_LITERAL;;
