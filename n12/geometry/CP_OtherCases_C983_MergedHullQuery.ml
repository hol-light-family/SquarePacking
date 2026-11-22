(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/MergedHullQuery.lean.        *)
(* The exact mixed hull that the larger C983 F/G allowances require: the    *)
(* checked_local_query mergedF3G6 (mask 2304, kind 2, owned {3,16}, a .hull *)
(* query), registered with slq_new (SharedLocalQueries.ml): the kernel      *)
(* re-proves it from its three hull points (inside) and target (outside).   *)
(* C983MHQ_MERGEDF3G6 : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>  *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits 2304) *)
(*   ==> auxown 2 c1 c2 a b l = set_of_list [3; 16] ==> F  (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: mergedF3G6 (with mergedF3G6_checked, mergedF3G6_certified) *)
let C983MHQ_MERGEDF3G6 = slq_new (2304, 2, [3; 16],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
