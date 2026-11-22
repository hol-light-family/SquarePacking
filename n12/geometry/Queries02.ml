(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Queries02.lean                     *)
(* (N12Compact.C981DomainSubset): exact inherited local queries.  Each Lean *)
(* checked_local_query is registered with slq_new (SharedLocalQueries.ml):  *)
(* the HOL kernel re-proves the query from its inside / outside points     *)
(* (a .hull query: its three hull points inside, its fourth point outside; *)
(* a .four query: the transformed FourPointDatum A, B inside, P, E outside; *)
(* a .short query: its cluster points inside, the pattern points outside).  *)
(* C981DSQ_QUERY976_N : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>  *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query976_264 *)
let C981DSQ_QUERY976_264 = slq_new (192, 1, [6],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_265 *)
let C981DSQ_QUERY976_265 = slq_new (192, 1, [7],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query976_266 *)
let C981DSQ_QUERY976_266 = slq_new (192, 1, [8],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_267 *)
let C981DSQ_QUERY976_267 = slq_new (192, 1, [9],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_268 *)
let C981DSQ_QUERY976_268 = slq_new (192, 2, [14],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "8/5", nlin_rat "3")]);;
(* Lean: query976_269 *)
let C981DSQ_QUERY976_269 = slq_new (192, 2, [1],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query976_270 *)
let C981DSQ_QUERY976_270 = slq_new (192, 2, [1; 14],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query976_561 *)
let C981DSQ_QUERY976_561 = slq_new (1024, 0, [0],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query976_562 *)
let C981DSQ_QUERY976_562 = slq_new (1024, 0, [1],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_563 *)
let C981DSQ_QUERY976_563 = slq_new (1024, 0, [0; 1],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_564 *)
let C981DSQ_QUERY976_564 = slq_new (1024, 0, [2],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_565 *)
let C981DSQ_QUERY976_565 = slq_new (1024, 0, [0; 2],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_566 *)
let C981DSQ_QUERY976_566 = slq_new (1024, 0, [1; 2],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_567 *)
let C981DSQ_QUERY976_567 = slq_new (1024, 0, [3],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_568 *)
let C981DSQ_QUERY976_568 = slq_new (1024, 0, [0; 3],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_569 *)
let C981DSQ_QUERY976_569 = slq_new (1024, 0, [1; 3],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_570 *)
let C981DSQ_QUERY976_570 = slq_new (1024, 0, [2; 3],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_571 *)
let C981DSQ_QUERY976_571 = slq_new (1024, 0, [4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_572 *)
let C981DSQ_QUERY976_572 = slq_new (1024, 0, [0; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_573 *)
let C981DSQ_QUERY976_573 = slq_new (1024, 0, [1; 4],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_574 *)
let C981DSQ_QUERY976_574 = slq_new (1024, 0, [2; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_575 *)
let C981DSQ_QUERY976_575 = slq_new (1024, 0, [3; 4],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_576 *)
let C981DSQ_QUERY976_576 = slq_new (1024, 0, [0; 5],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query976_577 *)
let C981DSQ_QUERY976_577 = slq_new (1024, 0, [1; 5],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query976_578 *)
let C981DSQ_QUERY976_578 = slq_new (1024, 0, [2; 5],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
