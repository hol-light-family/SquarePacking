(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components05/GDomain.lean     *)
(* (namespace N12Compact.Completion.OtherCases.C983.Component05Data).       *)
(* MonotoneQueries.SingleDomain gSingle5 = dsd record c983c05gd_gSingle5;    *)
(* Lean gChecked5 (gSingle5.Check family 1 gSignatures5, a decide) is the    *)
(* checked domain  C983C05GD_GCHECKED5 : |- hdom c983ri_family 512 1 [..]    *)
(* by mq_single (gSignatures5 = signatures of gQueries5 is checked in        *)
(* GQueries by c983c05gq_exact).                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_Components05_GQueries.ml";;

(* Lean: gSingle5 *)
let c983c05gd_gSingle5 =
  {dmask = 512; dlower = 1; dupper = 2;
   dallowed = [[5]; [6]; [8]; [2; 5]; [2; 6]; [3; 5]; [3; 6]; [5; 6]; [5; 8]; [6; 8]; [6; 9]];
   dqueries = c983c05gq_gQueries5};;

(* Lean: gChecked5 *)
let C983C05GD_GCHECKED5 = mq_single `c983ri_family` 1 c983c05gd_gSingle5;;
