(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/InitialDomains.lean.         *)
(* initialNamed : List (DomainTransport.NamedDomain family) is the OCaml     *)
(* list C983ID_INITIAL_NAMED of NamedDomain pairs                            *)
(* (|- cdom c983ri_family m al, |- m IN c983ri_family), in the Lean order    *)
(* initial0 .. initial11.  Tag C983ID_.                                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_Components00.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components01.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components02.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components03.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components04.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components05.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components06.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components07.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components08.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components09.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components10.ml";;
needs "n12/geometry/CP_OtherCases_C983_Components11.ml";;

(* Lean: initialNamed *)
let C983ID_INITIAL_NAMED : (thm * thm) list =
  [C983C00_INITIAL; C983C01_INITIAL; C983C02_INITIAL; C983C03_INITIAL; C983C04_INITIAL;
   C983C05_INITIAL5; C983C06_INITIAL6; C983C07_INITIAL; C983C08_INITIAL; C983C09_INITIAL;
   C983C10_INITIAL; C983C11_INITIAL];;
