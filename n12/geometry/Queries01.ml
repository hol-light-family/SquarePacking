(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Queries01.lean                     *)
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

(* Lean: query976_239 *)
let C981DSQ_QUERY976_239 = slq_new (48, 0, [6],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_240 *)
let C981DSQ_QUERY976_240 = slq_new (48, 0, [8],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query976_241 *)
let C981DSQ_QUERY976_241 = slq_new (48, 1, [0],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_242 *)
let C981DSQ_QUERY976_242 = slq_new (48, 1, [1],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_243 *)
let C981DSQ_QUERY976_243 = slq_new (48, 1, [2],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_244 *)
let C981DSQ_QUERY976_244 = slq_new (48, 1, [3],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_245 *)
let C981DSQ_QUERY976_245 = slq_new (48, 1, [4],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query976_246 *)
let C981DSQ_QUERY976_246 = slq_new (48, 1, [5],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_247 *)
let C981DSQ_QUERY976_247 = slq_new (48, 1, [6],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query976_248 *)
let C981DSQ_QUERY976_248 = slq_new (48, 1, [8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query976_249 *)
let C981DSQ_QUERY976_249 = slq_new (48, 2, [17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
(* Lean: query976_250 *)
let C981DSQ_QUERY976_250 = slq_new (48, 2, [9],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query976_251 *)
let C981DSQ_QUERY976_251 = slq_new (48, 2, [9; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
(* Lean: query976_252 *)
let C981DSQ_QUERY976_252 = slq_new (192, 0, [0],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query976_253 *)
let C981DSQ_QUERY976_253 = slq_new (192, 0, [2],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_254 *)
let C981DSQ_QUERY976_254 = slq_new (192, 0, [4],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_255 *)
let C981DSQ_QUERY976_255 = slq_new (192, 0, [5],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_256 *)
let C981DSQ_QUERY976_256 = slq_new (192, 0, [6],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_257 *)
let C981DSQ_QUERY976_257 = slq_new (192, 0, [7],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "8/5", nlin_rat "3")]);;
(* Lean: query976_258 *)
let C981DSQ_QUERY976_258 = slq_new (192, 0, [8],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_259 *)
let C981DSQ_QUERY976_259 = slq_new (192, 0, [9],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_260 *)
let C981DSQ_QUERY976_260 = slq_new (192, 1, [0],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query976_261 *)
let C981DSQ_QUERY976_261 = slq_new (192, 1, [2],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_262 *)
let C981DSQ_QUERY976_262 = slq_new (192, 1, [3],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_263 *)
let C981DSQ_QUERY976_263 = slq_new (192, 1, [5],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
