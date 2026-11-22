(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk03.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel, giving (mask, kind, owned,       *)
(* |- LocalQuery.sound) and registering it in LQ_TABLE.  The Lean import      *)
(* EntryQueryChunks.Imports is covered by Cases_C979_EntryQueryBase.ml        *)
(* (SharedLocalQueries); the historical query imports are not used here.     *)
(* Tag C979SS03_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;

(* Lean: selected48 *)
let C979SS03_SELECTED48 = slq_select 48;;

(* Lean: selected49 *)
let C979SS03_SELECTED49 = slq_select 49;;

(* Lean: selected50 *)
let C979SS03_SELECTED50 = slq_select 50;;

(* Lean: selected51 *)
let C979SS03_SELECTED51 = slq_select 51;;

(* Lean: selected52 *)
let C979SS03_SELECTED52 = slq_select 52;;

(* Lean: selected53 *)
let C979SS03_SELECTED53 = slq_select 53;;

(* Lean: selected54 *)
let C979SS03_SELECTED54 = slq_select 54;;

(* Lean: selected55 *)
let C979SS03_SELECTED55 = slq_select 55;;

(* Lean: selected56 *)
let C979SS03_SELECTED56 = slq_select 56;;

(* Lean: selected57 *)
let C979SS03_SELECTED57 = slq_select 57;;

(* Lean: selected58 *)
let C979SS03_SELECTED58 = slq_select 58;;

(* Lean: selected59 *)
let C979SS03_SELECTED59 = slq_select 59;;

(* Lean: selected60 *)
let C979SS03_SELECTED60 = slq_select 60;;

(* Lean: selected61 *)
let C979SS03_SELECTED61 = slq_select 61;;

(* Lean: selected62 *)
let C979SS03_SELECTED62 = slq_select 62;;

(* Lean: selected63 *)
let C979SS03_SELECTED63 = slq_select 63;;
