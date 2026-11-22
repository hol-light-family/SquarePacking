(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Prefix09.lean                       *)
(* (S12Completion.C981.Coverage.step09).  prefix09 is the Data table          *)
(* c981cov_prefix09 (CC_C981_Coverage_Data_Prefix09.ml, chunks of FinsetPool  *)
(* constants); it is first evaluated to a literal table                      *)
(* (C981CP09_PREFIX09_LITERAL), then StepCheck is proved by the producer      *)
(* c981cov_step_check (Prefix01.ml; Lean stepCheck_of_extensions_eq + rfl).   *)
(* Tag C981CP09_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Prefix01.ml";;
needs "n12/geometry/Prefix08.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09.ml";;

(* the FinsetPool definitions c981fp_fsNN *)
let C981CP09_POOL =
  filter (fun th -> try let c = fst (strip_comb (lhs (snd (strip_forall (concl th))))) in
                        let n = fst (dest_const c) in
                        String.length n > 9 && String.sub n 0 9 = "c981fp_fs"
                    with Failure _ -> false) (definitions ());;

(* APPEND L0 (APPEND L1 (.. Ln)) of literal lists, evaluated innermost first *)
let rec c981cov_appchain_conv tm =
  if (try fst (dest_const (fst (strip_comb tm))) = "APPEND" with Failure _ -> false)
  then (RAND_CONV c981cov_appchain_conv THENC c981cov_append_conv) tm
  else REFL tm;;

(* |- c981cov_prefix09 = [literal table] *)
let C981CP09_PREFIX09_LITERAL =
  (REWR_CONV c981cov_prefix09 THENC
   REWRITE_CONV[c981cov_prefix09chunk000; c981cov_prefix09chunk001; c981cov_prefix09chunk002;
                c981cov_prefix09chunk003; c981cov_prefix09chunk004; c981cov_prefix09chunk005;
                c981cov_prefix09chunk006; c981cov_prefix09chunk007; c981cov_prefix09chunk008] THENC
   REWRITE_CONV C981CP09_POOL THENC c981cov_appchain_conv) `c981cov_prefix09`;;

(* Lean: step09 *)
let C981CP09_STEP09 =
  c981cov_step_check c981cov_prefix08 c981cov_allowed4 C981CP09_PREFIX09_LITERAL;;
