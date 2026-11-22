(* ========================================================================= *)
(* Phase 2: Compact/Cases/C701/EntryQueryBase.lean (namespace S12).          *)
(* The literal C701 family and the list-checking helper c701_query_at.      *)
(* A Lean LocalQuery is the slq_new data (mask, kind, owned, inside points,  *)
(* outside points) of SharedLocalQueries.ml; "queries.all Check = true" is   *)
(* the HOL kernel re-proving every query, so c701_query_at is the producer   *)
(* c701eqb_query_at qs i, returning the re-proved LocalQuery.sound theorem   *)
(* of entry i (it fails exactly when the Lean check of that entry fails).    *)
(* Tag C701EQB_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: case701Family *)
let c701eqb_family = new_definition
 `c701eqb_family = {1, 2, 12, 16, 32, 192, 256, 1536, 4096, 8192, 16384, 34816}`;;

(* Lean: c701_query_at *)
let c701eqb_query_at qs i =
  if i < 0 || i >= length qs then failwith "c701eqb_query_at: index" else
  slq_new (el i qs);;
