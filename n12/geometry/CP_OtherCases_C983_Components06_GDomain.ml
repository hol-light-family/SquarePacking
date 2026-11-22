(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components06/GDomain.lean     *)
(* (namespace N12Compact.Completion.OtherCases.C983.Component06Data).       *)
(* MonotoneQueries.SingleDomain gSingle6 = dsd record c983c06gd_gSingle6;    *)
(* Lean gChecked6 (gSingle6.Check family 1 gSignatures6, a decide) is the    *)
(* checked domain  C983C06GD_GCHECKED6 : |- hdom c983ri_family 1024 1 [..]   *)
(* by mq_single (gSignatures6 = signatures of gQueries6 is checked in        *)
(* GQueries by c983c06gq_exact).                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_Components06_GQueries.ml";;

(* Lean: gSingle6 *)
let c983c06gd_gSingle6 =
  {dmask = 1024; dlower = 1; dupper = 2;
   dallowed = [[6]; [7]; [9]; [3; 6]; [3; 7]; [4; 6]; [4; 7]; [6; 7]; [6; 8]; [6; 9]; [7; 9]];
   dqueries = c983c06gq_gQueries6};;

(* Lean: gChecked6 *)
let C983C06GD_GCHECKED6 = mq_single `c983ri_family` 1 c983c06gd_gSingle6;;
