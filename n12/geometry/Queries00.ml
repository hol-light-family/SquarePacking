(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Queries00.lean                     *)
(* (N12Compact.C981DomainSubset): exact inherited local queries.  Each Lean *)
(* checked_local_query is registered with slq_new (SharedLocalQueries.ml):  *)
(* the HOL kernel re-proves the query from its inside / outside points     *)
(* (a .hull query: its three hull points inside, its fourth point outside; *)
(* a .four query: the transformed FourPointDatum A, B inside, P, E outside).*)
(* C981DSQ_QUERY976_N : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>  *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query976_214 *)
let C981DSQ_QUERY976_214 = slq_new (12, 0, [0],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_215 *)
let C981DSQ_QUERY976_215 = slq_new (12, 0, [1],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_216 *)
let C981DSQ_QUERY976_216 = slq_new (12, 0, [2],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]);;
(* Lean: query976_217 *)
let C981DSQ_QUERY976_217 = slq_new (12, 0, [3],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_218 *)
let C981DSQ_QUERY976_218 = slq_new (12, 0, [4],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_219 *)
let C981DSQ_QUERY976_219 = slq_new (12, 0, [5],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_220 *)
let C981DSQ_QUERY976_220 = slq_new (12, 0, [7],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_221 *)
let C981DSQ_QUERY976_221 = slq_new (12, 0, [9],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query976_222 *)
let C981DSQ_QUERY976_222 = slq_new (12, 1, [0],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_223 *)
let C981DSQ_QUERY976_223 = slq_new (12, 1, [1],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_224 *)
let C981DSQ_QUERY976_224 = slq_new (12, 1, [2],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query976_225 *)
let C981DSQ_QUERY976_225 = slq_new (12, 1, [3],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_226 *)
let C981DSQ_QUERY976_226 = slq_new (12, 1, [4],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_227 *)
let C981DSQ_QUERY976_227 = slq_new (12, 1, [6],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_228 *)
let C981DSQ_QUERY976_228 = slq_new (12, 1, [7],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_229 *)
let C981DSQ_QUERY976_229 = slq_new (12, 1, [9],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5")]);;
(* Lean: query976_230 *)
let C981DSQ_QUERY976_230 = slq_new (12, 2, [15],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]);;
(* Lean: query976_231 *)
let C981DSQ_QUERY976_231 = slq_new (12, 2, [8],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "8/5")]);;
(* Lean: query976_232 *)
let C981DSQ_QUERY976_232 = slq_new (12, 2, [8; 15],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]);;
(* Lean: query976_233 *)
let C981DSQ_QUERY976_233 = slq_new (48, 0, [0],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_234 *)
let C981DSQ_QUERY976_234 = slq_new (48, 0, [1],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_235 *)
let C981DSQ_QUERY976_235 = slq_new (48, 0, [2],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_236 *)
let C981DSQ_QUERY976_236 = slq_new (48, 0, [3],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
(* Lean: query976_237 *)
let C981DSQ_QUERY976_237 = slq_new (48, 0, [4],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_238 *)
let C981DSQ_QUERY976_238 = slq_new (48, 0, [5],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
