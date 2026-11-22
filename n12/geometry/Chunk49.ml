(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk49.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel.  Lean import Chunk48.            *)
(* Tag C979SS49_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Chunk48.ml";;

(* Lean: selected1633 *)
let C979SS49_SELECTED1633 = slq_select 1633;;

(* Lean: selected1634 *)
let C979SS49_SELECTED1634 = slq_select 1634;;
