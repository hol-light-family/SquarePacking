(* ========================================================================= *)
(* Phase 2: Compact/Cases/C973/EntryQueryBase.lean (namespace S12).          *)
(* The literal C973 family and the list-checking helper c973_query_at.      *)
(* A Lean LocalQuery is the slq_new data (mask, kind, owned, inside points,  *)
(* outside points) of SharedLocalQueries.ml; "queries.all Check = true" is   *)
(* the HOL kernel re-proving every query, so c973_query_at is the producer   *)
(* c973eqb_query_at qs i, returning the re-proved LocalQuery.sound theorem   *)
(* of entry i (it fails exactly when the Lean check of that entry fails).    *)
(* Tag C973EQB_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: case973Family *)
let c973eqb_family = new_definition
 `c973eqb_family = {1, 2, 12, 48, 192, 256, 512, 1024, 2048, 4096, 16384, 32768}`;;

(* Lean: c973_query_at *)
let c973eqb_query_at qs i =
  if i < 0 || i >= length qs then failwith "c973eqb_query_at: index" else
  slq_new (el i qs);;
