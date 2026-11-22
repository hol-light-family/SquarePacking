(* ========================================================================= *)
(* Phase 2: Compact/Cases/C717/EntryQueryBase.lean (namespace S12).          *)
(* The literal C717 family and the list-checking helper c717_query_at.      *)
(* A Lean LocalQuery is the slq_new data (mask, kind, owned, inside points,  *)
(* outside points) of SharedLocalQueries.ml; "queries.all Check = true" is   *)
(* the HOL kernel re-proving every query, so c717_query_at is the producer   *)
(* c717eqb_query_at qs i, returning the re-proved LocalQuery.sound theorem   *)
(* of entry i (it fails exactly when the Lean check of that entry fails).    *)
(* Tag C717EQB_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: case717Family *)
let c717eqb_family = new_definition
 `c717eqb_family = {1, 2, 12, 16, 32, 192, 768, 3072, 4096, 8192, 16384, 32768}`;;

(* Lean: c717_query_at *)
let c717eqb_query_at qs i =
  if i < 0 || i >= length qs then failwith "c717eqb_query_at: index" else
  slq_new (el i qs);;
