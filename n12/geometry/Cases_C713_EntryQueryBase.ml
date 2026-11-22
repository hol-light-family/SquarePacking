(* ========================================================================= *)
(* Phase 2: Compact/Cases/C713/EntryQueryBase.lean (namespace S12).          *)
(* The literal C713 family and the list-checking helper c713_query_at.      *)
(* A Lean LocalQuery is the slq_new data (mask, kind, owned, inside points,  *)
(* outside points) of SharedLocalQueries.ml; "queries.all Check = true" is   *)
(* the HOL kernel re-proving every query, so c713_query_at is the producer   *)
(* c713eqb_query_at qs i, returning the re-proved LocalQuery.sound theorem   *)
(* of entry i (it fails exactly when the Lean check of that entry fails).    *)
(* Tag C713EQB_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: case713Family *)
let c713eqb_family = new_definition
 `c713eqb_family = {1, 2, 12, 16, 32, 192, 512, 2304, 4096, 8192, 16384, 32768}`;;

(* Lean: c713_query_at *)
let c713eqb_query_at qs i =
  if i < 0 || i >= length qs then failwith "c713eqb_query_at: index" else
  slq_new (el i qs);;
