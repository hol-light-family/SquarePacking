(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components05/FDomain.lean     *)
(* (namespace N12Compact.Completion.OtherCases.C983.Component05Data).       *)
(* MonotoneQueries.SingleDomain fSingle5 = dsd record c983c05fd_fSingle5;    *)
(* Lean fChecked5 (fSingle5.Check family 0 fSignatures5, a decide) is the    *)
(* checked domain  C983C05FD_FCHECKED5 : |- hdom c983ri_family 512 0 [..]    *)
(* by mq_single (which performs Check: budget bounds and every small owner   *)
(* set allowed or refuted by a compatible query; fSignatures5 = signatures   *)
(* of fQueries5 is the c983c05fq_exact check in FQueries).                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_Components05_FQueries.ml";;

(* Lean: fSingle5 *)
let c983c05fd_fSingle5 =
  {dmask = 512; dlower = 1; dupper = 3;
   dallowed = [[4]; [6]; [8]; [2; 4]; [4; 5]; [4; 6]; [4; 8]; [4; 9]; [5; 8]; [6; 8]; [8; 9];
               [0; 4; 5]; [1; 4; 5]; [1; 5; 8]; [2; 4; 5]; [2; 4; 6]; [2; 4; 8]; [2; 4; 9];
               [4; 5; 6]; [4; 5; 8]; [4; 5; 9]; [4; 6; 8]; [4; 6; 9]; [4; 8; 9]; [5; 6; 8];
               [5; 8; 9]; [6; 8; 9]];
   dqueries = c983c05fq_fQueries5};;

(* Lean: fChecked5 *)
let C983C05FD_FCHECKED5 = mq_single `c983ri_family` 0 c983c05fd_fSingle5;;
