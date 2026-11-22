(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components06/FDomain.lean     *)
(* (namespace N12Compact.Completion.OtherCases.C983.Component06Data).       *)
(* MonotoneQueries.SingleDomain fSingle6 = dsd record c983c06fd_fSingle6;    *)
(* Lean fChecked6 (fSingle6.Check family 0 fSignatures6, a decide) is the    *)
(* checked domain  C983C06FD_FCHECKED6 : |- hdom c983ri_family 1024 0 [..]   *)
(* by mq_single (which performs Check: budget bounds and every small owner   *)
(* set allowed or refuted by a compatible query; fSignatures6 = signatures   *)
(* of fQueries6 is the c983c06fq_exact check in FQueries).                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_Components06_FQueries.ml";;

(* Lean: fSingle6 *)
let c983c06fd_fSingle6 =
  {dmask = 1024; dlower = 1; dupper = 3;
   dallowed = [[5]; [7]; [9]; [3; 5]; [4; 5]; [4; 9]; [5; 7]; [5; 8]; [5; 9]; [7; 9]; [8; 9];
               [0; 4; 5]; [0; 4; 9]; [1; 4; 5]; [3; 4; 5]; [3; 5; 7]; [3; 5; 8]; [3; 5; 9];
               [4; 5; 7]; [4; 5; 8]; [4; 5; 9]; [4; 7; 9]; [4; 8; 9]; [5; 7; 8]; [5; 7; 9];
               [5; 8; 9]; [7; 8; 9]];
   dqueries = c983c06fq_fQueries6};;

(* Lean: fChecked6 *)
let C983C06FD_FCHECKED6 = mq_single `c983ri_family` 0 c983c06fd_fSingle6;;
