(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk08.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel, giving (mask, kind, owned,       *)
(* |- LocalQuery.sound) and registering it in LQ_TABLE.  The Lean import      *)
(* EntryQueryChunks.Imports is covered by Cases_C979_EntryQueryBase.ml        *)
(* (SharedLocalQueries); the historical query imports are not used here.     *)
(* Tag C979SS08_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;

(* Lean: selected128 *)
let C979SS08_SELECTED128 = slq_select 128;;

(* Lean: selected129 *)
let C979SS08_SELECTED129 = slq_select 129;;

(* Lean: selected130 *)
let C979SS08_SELECTED130 = slq_select 130;;

(* Lean: selected131 *)
let C979SS08_SELECTED131 = slq_select 131;;

(* Lean: selected132 *)
let C979SS08_SELECTED132 = slq_select 132;;

(* Lean: selected133 *)
let C979SS08_SELECTED133 = slq_select 133;;

(* Lean: selected134 *)
let C979SS08_SELECTED134 = slq_select 134;;

(* Lean: selected135 *)
let C979SS08_SELECTED135 = slq_select 135;;

(* Lean: selected136 *)
let C979SS08_SELECTED136 = slq_select 136;;

(* Lean: selected137 *)
let C979SS08_SELECTED137 = slq_select 137;;

(* Lean: selected138 *)
let C979SS08_SELECTED138 = slq_select 138;;

(* Lean: selected139 *)
let C979SS08_SELECTED139 = slq_select 139;;

(* Lean: selected140 *)
let C979SS08_SELECTED140 = slq_select 140;;

(* Lean: selected141 *)
let C979SS08_SELECTED141 = slq_select 141;;

(* Lean: selected142 *)
let C979SS08_SELECTED142 = slq_select 142;;

(* Lean: selected143 *)
let C979SS08_SELECTED143 = slq_select 143;;
