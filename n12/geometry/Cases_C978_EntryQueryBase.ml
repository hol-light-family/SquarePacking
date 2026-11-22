(* ========================================================================= *)
(* Phase 2: Compact/Cases/C978/EntryQueryBase.lean (namespace S12).          *)
(* The literal C978 family and the list-checking helper c978_query_at.      *)
(* A Lean LocalQuery is the slq_new data (mask, kind, owned, inside points,  *)
(* outside points) of SharedLocalQueries.ml; "queries.all Check = true" is   *)
(* the HOL kernel re-proving every query, so c978_query_at is the producer   *)
(* c978eqb_query_at qs i, returning the re-proved LocalQuery.sound theorem   *)
(* of entry i (it fails exactly when the Lean check of that entry fails).    *)
(* Tag C978EQB_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: case978Family *)
let c978eqb_family = new_definition
 `c978eqb_family = {1, 2, 12, 48, 192, 256, 512, 2048, 4096, 8192, 16384, 33792}`;;

(* Lean: c978_query_at *)
let c978eqb_query_at qs i =
  if i < 0 || i >= length qs then failwith "c978eqb_query_at: index" else
  slq_new (el i qs);;
