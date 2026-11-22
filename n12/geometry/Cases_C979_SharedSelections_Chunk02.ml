(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk02.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel, giving (mask, kind, owned,       *)
(* |- LocalQuery.sound) and registering it in LQ_TABLE.  The Lean import      *)
(* EntryQueryChunks.Imports is covered by Cases_C979_EntryQueryBase.ml        *)
(* (SharedLocalQueries); the historical query imports are not used here.     *)
(* Tag C979SS02_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;

(* Lean: selected32 *)
let C979SS02_SELECTED32 = slq_select 32;;

(* Lean: selected33 *)
let C979SS02_SELECTED33 = slq_select 33;;

(* Lean: selected34 *)
let C979SS02_SELECTED34 = slq_select 34;;

(* Lean: selected35 *)
let C979SS02_SELECTED35 = slq_select 35;;

(* Lean: selected36 *)
let C979SS02_SELECTED36 = slq_select 36;;

(* Lean: selected37 *)
let C979SS02_SELECTED37 = slq_select 37;;

(* Lean: selected38 *)
let C979SS02_SELECTED38 = slq_select 38;;

(* Lean: selected39 *)
let C979SS02_SELECTED39 = slq_select 39;;

(* Lean: selected40 *)
let C979SS02_SELECTED40 = slq_select 40;;

(* Lean: selected41 *)
let C979SS02_SELECTED41 = slq_select 41;;

(* Lean: selected42 *)
let C979SS02_SELECTED42 = slq_select 42;;

(* Lean: selected43 *)
let C979SS02_SELECTED43 = slq_select 43;;

(* Lean: selected44 *)
let C979SS02_SELECTED44 = slq_select 44;;

(* Lean: selected45 *)
let C979SS02_SELECTED45 = slq_select 45;;

(* Lean: selected46 *)
let C979SS02_SELECTED46 = slq_select 46;;

(* Lean: selected47 *)
let C979SS02_SELECTED47 = slq_select 47;;
