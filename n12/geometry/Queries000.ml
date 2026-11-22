(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries000.lean *)
(* (N12Compact.HistoricalOwnership.Queries): exact inherited local queries.  Each Lean *)
(* checked_local_query is registered with slq_hist n (SharedLocalQueries.ml):*)
(* the HOL kernel re-proves the query from its inside / outside points     *)
(* (a .hull query: its three hull points inside, its fourth point outside; *)
(* a .four query: the transformed FourPointDatum A, B inside, P, E outside; *)
(* a .short query: its cluster points inside, the pattern points outside).  *)
(* HOQ_QUERYn : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>  *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query0 *)
let HOQ_QUERY0 = slq_hist 0 (12, 0, [0],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1 *)
let HOQ_QUERY1 = slq_hist 1 (12, 0, [1],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query2 *)
let HOQ_QUERY2 = slq_hist 2 (12, 0, [2],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]);;
(* Lean: query3 *)
let HOQ_QUERY3 = slq_hist 3 (12, 0, [3],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query4 *)
let HOQ_QUERY4 = slq_hist 4 (12, 0, [4],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query5 *)
let HOQ_QUERY5 = slq_hist 5 (12, 0, [5],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query6 *)
let HOQ_QUERY6 = slq_hist 6 (12, 0, [7],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query7 *)
let HOQ_QUERY7 = slq_hist 7 (12, 0, [9],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query8 *)
let HOQ_QUERY8 = slq_hist 8 (12, 2, [8],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "8/5")]);;
(* Lean: query9 *)
let HOQ_QUERY9 = slq_hist 9 (32, 0, [0; 1],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query10 *)
let HOQ_QUERY10 = slq_hist 10 (32, 0, [0; 2],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query11 *)
let HOQ_QUERY11 = slq_hist 11 (32, 0, [1; 2],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query12 *)
let HOQ_QUERY12 = slq_hist 12 (32, 0, [0; 3],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query13 *)
let HOQ_QUERY13 = slq_hist 13 (32, 0, [1; 3],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query14 *)
let HOQ_QUERY14 = slq_hist 14 (32, 0, [2; 3],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query15 *)
let HOQ_QUERY15 = slq_hist 15 (32, 0, [0; 4],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query16 *)
let HOQ_QUERY16 = slq_hist 16 (32, 0, [1; 4],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query17 *)
let HOQ_QUERY17 = slq_hist 17 (32, 0, [2; 4],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query18 *)
let HOQ_QUERY18 = slq_hist 18 (32, 0, [3; 4],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query19 *)
let HOQ_QUERY19 = slq_hist 19 (32, 0, [0; 5],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query20 *)
let HOQ_QUERY20 = slq_hist 20 (32, 0, [1; 5],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query21 *)
let HOQ_QUERY21 = slq_hist 21 (32, 0, [2; 5],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query22 *)
let HOQ_QUERY22 = slq_hist 22 (32, 0, [3; 5],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query23 *)
let HOQ_QUERY23 = slq_hist 23 (32, 0, [4; 5],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query24 *)
let HOQ_QUERY24 = slq_hist 24 (32, 0, [0; 6],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query25 *)
let HOQ_QUERY25 = slq_hist 25 (32, 0, [1; 6],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query26 *)
let HOQ_QUERY26 = slq_hist 26 (32, 0, [2; 6],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query27 *)
let HOQ_QUERY27 = slq_hist 27 (32, 0, [3; 6],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query28 *)
let HOQ_QUERY28 = slq_hist 28 (32, 0, [4; 6],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query29 *)
let HOQ_QUERY29 = slq_hist 29 (32, 0, [5; 6],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query30 *)
let HOQ_QUERY30 = slq_hist 30 (32, 0, [0; 7],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query31 *)
let HOQ_QUERY31 = slq_hist 31 (32, 0, [1; 7],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
