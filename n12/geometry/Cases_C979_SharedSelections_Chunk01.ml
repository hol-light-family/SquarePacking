(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk01.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel, giving (mask, kind, owned,       *)
(* |- LocalQuery.sound) and registering it in LQ_TABLE.  The Lean import      *)
(* EntryQueryChunks.Imports is covered by Cases_C979_EntryQueryBase.ml        *)
(* (SharedLocalQueries); the historical query imports are not used here.     *)
(* Tag C979SS01_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;

(* Lean: selected16 *)
let C979SS01_SELECTED16 = slq_select 16;;

(* Lean: selected17 *)
let C979SS01_SELECTED17 = slq_select 17;;

(* Lean: selected18 *)
let C979SS01_SELECTED18 = slq_select 18;;

(* Lean: selected19 *)
let C979SS01_SELECTED19 = slq_select 19;;

(* Lean: selected20 *)
let C979SS01_SELECTED20 = slq_select 20;;

(* Lean: selected21 *)
let C979SS01_SELECTED21 = slq_select 21;;

(* Lean: selected22 *)
let C979SS01_SELECTED22 = slq_select 22;;

(* Lean: selected23 *)
let C979SS01_SELECTED23 = slq_select 23;;

(* Lean: selected24 *)
let C979SS01_SELECTED24 = slq_select 24;;

(* Lean: selected25 *)
let C979SS01_SELECTED25 = slq_select 25;;

(* Lean: selected26 *)
let C979SS01_SELECTED26 = slq_select 26;;

(* Lean: selected27 *)
let C979SS01_SELECTED27 = slq_select 27;;

(* Lean: selected28 *)
let C979SS01_SELECTED28 = slq_select 28;;

(* Lean: selected29 *)
let C979SS01_SELECTED29 = slq_select 29;;

(* Lean: selected30 *)
let C979SS01_SELECTED30 = slq_select 30;;

(* Lean: selected31 *)
let C979SS01_SELECTED31 = slq_select 31;;
