(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk00.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel, giving (mask, kind, owned,       *)
(* |- LocalQuery.sound) and registering it in LQ_TABLE.  The Lean import      *)
(* EntryQueryChunks.Imports is covered by Cases_C979_EntryQueryBase.ml        *)
(* (SharedLocalQueries); the historical query imports are not used here.     *)
(* Tag C979SS00_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;

(* Lean: selected0 *)
let C979SS00_SELECTED0 = slq_select 0;;

(* Lean: selected1 *)
let C979SS00_SELECTED1 = slq_select 1;;

(* Lean: selected2 *)
let C979SS00_SELECTED2 = slq_select 2;;

(* Lean: selected3 *)
let C979SS00_SELECTED3 = slq_select 3;;

(* Lean: selected4 *)
let C979SS00_SELECTED4 = slq_select 4;;

(* Lean: selected5 *)
let C979SS00_SELECTED5 = slq_select 5;;

(* Lean: selected6 *)
let C979SS00_SELECTED6 = slq_select 6;;

(* Lean: selected7 *)
let C979SS00_SELECTED7 = slq_select 7;;

(* Lean: selected8 *)
let C979SS00_SELECTED8 = slq_select 8;;

(* Lean: selected9 *)
let C979SS00_SELECTED9 = slq_select 9;;

(* Lean: selected10 *)
let C979SS00_SELECTED10 = slq_select 10;;

(* Lean: selected11 *)
let C979SS00_SELECTED11 = slq_select 11;;

(* Lean: selected12 *)
let C979SS00_SELECTED12 = slq_select 12;;

(* Lean: selected13 *)
let C979SS00_SELECTED13 = slq_select 13;;

(* Lean: selected14 *)
let C979SS00_SELECTED14 = slq_select 14;;

(* Lean: selected15 *)
let C979SS00_SELECTED15 = slq_select 15;;
