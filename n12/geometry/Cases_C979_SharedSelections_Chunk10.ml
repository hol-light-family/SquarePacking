(* ========================================================================= *)
(* Port of Compact/Cases/C979/SharedSelections/Chunk10.lean                   *)
(* (N12Compact.C979SharedSelections).  Lean                                   *)
(*   noncomputable def selectedN : {q : LocalQuery // q.Check} :=             *)
(*     (certified_query% N)                                                   *)
(* is slq_select N (SharedLocalQueries.ml): the Phase-1 local query N of      *)
(* S12.localQueries re-proved by the kernel, giving (mask, kind, owned,       *)
(* |- LocalQuery.sound) and registering it in LQ_TABLE.  The Lean import      *)
(* EntryQueryChunks.Imports is covered by Cases_C979_EntryQueryBase.ml        *)
(* (SharedLocalQueries); the historical query imports are not used here.     *)
(* Tag C979SS10_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;

(* Lean: selected160 *)
let C979SS10_SELECTED160 = slq_select 160;;

(* Lean: selected161 *)
let C979SS10_SELECTED161 = slq_select 161;;

(* Lean: selected162 *)
let C979SS10_SELECTED162 = slq_select 162;;

(* Lean: selected163 *)
let C979SS10_SELECTED163 = slq_select 163;;

(* Lean: selected164 *)
let C979SS10_SELECTED164 = slq_select 164;;

(* Lean: selected165 *)
let C979SS10_SELECTED165 = slq_select 165;;

(* Lean: selected166 *)
let C979SS10_SELECTED166 = slq_select 166;;

(* Lean: selected167 *)
let C979SS10_SELECTED167 = slq_select 167;;

(* Lean: selected168 *)
let C979SS10_SELECTED168 = slq_select 168;;

(* Lean: selected169 *)
let C979SS10_SELECTED169 = slq_select 169;;

(* Lean: selected170 *)
let C979SS10_SELECTED170 = slq_select 170;;

(* Lean: selected171 *)
let C979SS10_SELECTED171 = slq_select 171;;

(* Lean: selected172 *)
let C979SS10_SELECTED172 = slq_select 172;;

(* Lean: selected173 *)
let C979SS10_SELECTED173 = slq_select 173;;

(* Lean: selected174 *)
let C979SS10_SELECTED174 = slq_select 174;;

(* Lean: selected175 *)
let C979SS10_SELECTED175 = slq_select 175;;
