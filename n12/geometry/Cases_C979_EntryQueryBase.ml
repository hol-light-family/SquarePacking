(* ========================================================================= *)
(* Phase 2: Compact/Cases/C979/EntryQueryBase.lean (namespace S12).          *)
(* The literal C979 family and the list-checking helper c979_query_at.      *)
(* A Lean LocalQuery is the slq_new data (mask, kind, owned, inside points,  *)
(* outside points) of SharedLocalQueries.ml; "queries.all Check = true" is   *)
(* the HOL kernel re-proving every query, so c979_query_at is the producer   *)
(* c979eqb_query_at qs i, returning the re-proved LocalQuery.sound theorem   *)
(* of entry i (it fails exactly when the Lean check of that entry fails).    *)
(* Tag C979EQB_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: case979Family *)
let c979eqb_family = new_definition
 `c979eqb_family = {1, 2, 12, 48, 192, 256, 512, 3072, 4096, 8192, 16384, 32768}`;;

(* Lean: c979_query_at *)
let c979eqb_query_at qs i =
  if i < 0 || i >= length qs then failwith "c979eqb_query_at: index" else
  slq_new (el i qs);;
