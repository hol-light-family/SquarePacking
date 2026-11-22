(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk06.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel, giving (mask, kind, owned,       *)
(* |- LocalQuery.sound) and registering it in LQ_TABLE.  The Lean import      *)
(* EntryQueryChunks.Imports is covered by Cases_C979_EntryQueryBase.ml        *)
(* (SharedLocalQueries); the historical query imports are not used here.     *)
(* Tag C979SS06_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;

(* Lean: selected96 *)
let C979SS06_SELECTED96 = slq_select 96;;

(* Lean: selected97 *)
let C979SS06_SELECTED97 = slq_select 97;;

(* Lean: selected98 *)
let C979SS06_SELECTED98 = slq_select 98;;

(* Lean: selected99 *)
let C979SS06_SELECTED99 = slq_select 99;;

(* Lean: selected100 *)
let C979SS06_SELECTED100 = slq_select 100;;

(* Lean: selected101 *)
let C979SS06_SELECTED101 = slq_select 101;;

(* Lean: selected102 *)
let C979SS06_SELECTED102 = slq_select 102;;

(* Lean: selected103 *)
let C979SS06_SELECTED103 = slq_select 103;;

(* Lean: selected104 *)
let C979SS06_SELECTED104 = slq_select 104;;

(* Lean: selected105 *)
let C979SS06_SELECTED105 = slq_select 105;;

(* Lean: selected106 *)
let C979SS06_SELECTED106 = slq_select 106;;

(* Lean: selected107 *)
let C979SS06_SELECTED107 = slq_select 107;;

(* Lean: selected108 *)
let C979SS06_SELECTED108 = slq_select 108;;

(* Lean: selected109 *)
let C979SS06_SELECTED109 = slq_select 109;;

(* Lean: selected110 *)
let C979SS06_SELECTED110 = slq_select 110;;

(* Lean: selected111 *)
let C979SS06_SELECTED111 = slq_select 111;;
