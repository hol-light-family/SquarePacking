(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk04.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel, giving (mask, kind, owned,       *)
(* |- LocalQuery.sound) and registering it in LQ_TABLE.  The Lean import      *)
(* EntryQueryChunks.Imports is covered by Cases_C979_EntryQueryBase.ml        *)
(* (SharedLocalQueries); the historical query imports are not used here.     *)
(* Tag C979SS04_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;

(* Lean: selected64 *)
let C979SS04_SELECTED64 = slq_select 64;;

(* Lean: selected65 *)
let C979SS04_SELECTED65 = slq_select 65;;

(* Lean: selected66 *)
let C979SS04_SELECTED66 = slq_select 66;;

(* Lean: selected67 *)
let C979SS04_SELECTED67 = slq_select 67;;

(* Lean: selected68 *)
let C979SS04_SELECTED68 = slq_select 68;;

(* Lean: selected69 *)
let C979SS04_SELECTED69 = slq_select 69;;

(* Lean: selected70 *)
let C979SS04_SELECTED70 = slq_select 70;;

(* Lean: selected71 *)
let C979SS04_SELECTED71 = slq_select 71;;

(* Lean: selected72 *)
let C979SS04_SELECTED72 = slq_select 72;;

(* Lean: selected73 *)
let C979SS04_SELECTED73 = slq_select 73;;

(* Lean: selected74 *)
let C979SS04_SELECTED74 = slq_select 74;;

(* Lean: selected75 *)
let C979SS04_SELECTED75 = slq_select 75;;

(* Lean: selected76 *)
let C979SS04_SELECTED76 = slq_select 76;;

(* Lean: selected77 *)
let C979SS04_SELECTED77 = slq_select 77;;

(* Lean: selected78 *)
let C979SS04_SELECTED78 = slq_select 78;;

(* Lean: selected79 *)
let C979SS04_SELECTED79 = slq_select 79;;
