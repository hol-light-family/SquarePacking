(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk05.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel, giving (mask, kind, owned,       *)
(* |- LocalQuery.sound) and registering it in LQ_TABLE.  The Lean import      *)
(* EntryQueryChunks.Imports is covered by Cases_C979_EntryQueryBase.ml        *)
(* (SharedLocalQueries); the historical query imports are not used here.     *)
(* Tag C979SS05_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;

(* Lean: selected80 *)
let C979SS05_SELECTED80 = slq_select 80;;

(* Lean: selected81 *)
let C979SS05_SELECTED81 = slq_select 81;;

(* Lean: selected82 *)
let C979SS05_SELECTED82 = slq_select 82;;

(* Lean: selected83 *)
let C979SS05_SELECTED83 = slq_select 83;;

(* Lean: selected84 *)
let C979SS05_SELECTED84 = slq_select 84;;

(* Lean: selected85 *)
let C979SS05_SELECTED85 = slq_select 85;;

(* Lean: selected86 *)
let C979SS05_SELECTED86 = slq_select 86;;

(* Lean: selected87 *)
let C979SS05_SELECTED87 = slq_select 87;;

(* Lean: selected88 *)
let C979SS05_SELECTED88 = slq_select 88;;

(* Lean: selected89 *)
let C979SS05_SELECTED89 = slq_select 89;;

(* Lean: selected90 *)
let C979SS05_SELECTED90 = slq_select 90;;

(* Lean: selected91 *)
let C979SS05_SELECTED91 = slq_select 91;;

(* Lean: selected92 *)
let C979SS05_SELECTED92 = slq_select 92;;

(* Lean: selected93 *)
let C979SS05_SELECTED93 = slq_select 93;;

(* Lean: selected94 *)
let C979SS05_SELECTED94 = slq_select 94;;

(* Lean: selected95 *)
let C979SS05_SELECTED95 = slq_select 95;;
