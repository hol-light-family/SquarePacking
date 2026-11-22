(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries002.lean                          *)
(* (N12Compact.HistoricalOwnership.Queries): exact historical local queries.*)
(* Each Lean checked_local_query is registered with slq_hist n               *)
(* (SharedLocalQueries.ml): the HOL kernel re-proves the query from its     *)
(* inside / outside points (a .hull query: its three hull points inside,    *)
(* its fourth point outside; a .four query: the transformed FourPointDatum *)
(* A, B inside, P, E outside; a .short query: its cluster points inside,   *)
(* the transformed pattern points outside).                                 *)
(* HOQ_QUERYN : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>          *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query64 *)
let HOQ_QUERY64 = slq_hist 64 (1536, 0, [2],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query65 *)
let HOQ_QUERY65 = slq_hist 65 (1536, 0, [3],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query66 *)
let HOQ_QUERY66 = slq_hist 66 (1536, 1, [0],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query67 *)
let HOQ_QUERY67 = slq_hist 67 (1536, 1, [1],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query68 *)
let HOQ_QUERY68 = slq_hist 68 (1536, 1, [2],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query69 *)
let HOQ_QUERY69 = slq_hist 69 (1536, 1, [3],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query70 *)
let HOQ_QUERY70 = slq_hist 70 (1536, 1, [4],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query71 *)
let HOQ_QUERY71 = slq_hist 71 (1536, 1, [5],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query72 *)
let HOQ_QUERY72 = slq_hist 72 (1536, 1, [7],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query73 *)
let HOQ_QUERY73 = slq_hist 73 (1536, 1, [8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query74 *)
let HOQ_QUERY74 = slq_hist 74 (1536, 1, [9],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query75 *)
let HOQ_QUERY75 = slq_hist 75 (34816, 0, [0],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query76 *)
let HOQ_QUERY76 = slq_hist 76 (34816, 0, [1],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query77 *)
let HOQ_QUERY77 = slq_hist 77 (34816, 0, [0; 1],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query78 *)
let HOQ_QUERY78 = slq_hist 78 (34816, 0, [2],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query79 *)
let HOQ_QUERY79 = slq_hist 79 (34816, 0, [0; 2],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query80 *)
let HOQ_QUERY80 = slq_hist 80 (34816, 0, [1; 2],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query81 *)
let HOQ_QUERY81 = slq_hist 81 (34816, 0, [0; 3],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query82 *)
let HOQ_QUERY82 = slq_hist 82 (34816, 0, [2; 3],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query83 *)
let HOQ_QUERY83 = slq_hist 83 (34816, 0, [4],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query84 *)
let HOQ_QUERY84 = slq_hist 84 (34816, 0, [0; 4],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query85 *)
let HOQ_QUERY85 = slq_hist 85 (34816, 0, [1; 4],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query86 *)
let HOQ_QUERY86 = slq_hist 86 (34816, 0, [2; 4],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query87 *)
let HOQ_QUERY87 = slq_hist 87 (34816, 0, [3; 4],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query88 *)
let HOQ_QUERY88 = slq_hist 88 (34816, 0, [2; 5],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query89 *)
let HOQ_QUERY89 = slq_hist 89 (34816, 0, [6],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query90 *)
let HOQ_QUERY90 = slq_hist 90 (34816, 0, [0; 6],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query91 *)
let HOQ_QUERY91 = slq_hist 91 (34816, 0, [1; 6],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query92 *)
let HOQ_QUERY92 = slq_hist 92 (34816, 0, [2; 6],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query93 *)
let HOQ_QUERY93 = slq_hist 93 (34816, 0, [3; 6],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query94 *)
let HOQ_QUERY94 = slq_hist 94 (34816, 0, [4; 6],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query95 *)
let HOQ_QUERY95 = slq_hist 95 (34816, 0, [5; 6],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
