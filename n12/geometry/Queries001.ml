(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries001.lean *)
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

(* Lean: query32 *)
let HOQ_QUERY32 = slq_hist 32 (32, 0, [2; 7],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query33 *)
let HOQ_QUERY33 = slq_hist 33 (32, 0, [3; 7],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query34 *)
let HOQ_QUERY34 = slq_hist 34 (32, 0, [4; 7],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query35 *)
let HOQ_QUERY35 = slq_hist 35 (32, 0, [5; 7],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query36 *)
let HOQ_QUERY36 = slq_hist 36 (32, 0, [6; 7],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query37 *)
let HOQ_QUERY37 = slq_hist 37 (32, 0, [0; 8],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query38 *)
let HOQ_QUERY38 = slq_hist 38 (32, 0, [1; 8],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query39 *)
let HOQ_QUERY39 = slq_hist 39 (32, 0, [2; 8],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query40 *)
let HOQ_QUERY40 = slq_hist 40 (32, 0, [3; 8],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query41 *)
let HOQ_QUERY41 = slq_hist 41 (32, 0, [4; 8],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query42 *)
let HOQ_QUERY42 = slq_hist 42 (32, 0, [5; 8],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query43 *)
let HOQ_QUERY43 = slq_hist 43 (32, 0, [6; 8],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "72/25")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query44 *)
let HOQ_QUERY44 = slq_hist 44 (32, 0, [7; 8],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query45 *)
let HOQ_QUERY45 = slq_hist 45 (32, 0, [0; 9],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query46 *)
let HOQ_QUERY46 = slq_hist 46 (32, 0, [1; 9],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query47 *)
let HOQ_QUERY47 = slq_hist 47 (32, 0, [2; 9],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query48 *)
let HOQ_QUERY48 = slq_hist 48 (32, 0, [3; 9],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
(* Lean: query49 *)
let HOQ_QUERY49 = slq_hist 49 (32, 0, [4; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query50 *)
let HOQ_QUERY50 = slq_hist 50 (32, 0, [5; 9],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query51 *)
let HOQ_QUERY51 = slq_hist 51 (32, 0, [6; 9],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2")]);;
(* Lean: query52 *)
let HOQ_QUERY52 = slq_hist 52 (32, 0, [8; 9],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2")]);;
(* Lean: query53 *)
let HOQ_QUERY53 = slq_hist 53 (192, 0, [0],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query54 *)
let HOQ_QUERY54 = slq_hist 54 (192, 0, [2],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query55 *)
let HOQ_QUERY55 = slq_hist 55 (192, 0, [4],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query56 *)
let HOQ_QUERY56 = slq_hist 56 (192, 0, [5],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query57 *)
let HOQ_QUERY57 = slq_hist 57 (192, 0, [6],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query58 *)
let HOQ_QUERY58 = slq_hist 58 (192, 0, [7],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "8/5", nlin_rat "3")]);;
(* Lean: query59 *)
let HOQ_QUERY59 = slq_hist 59 (192, 0, [8],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query60 *)
let HOQ_QUERY60 = slq_hist 60 (192, 0, [9],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query61 *)
let HOQ_QUERY61 = slq_hist 61 (192, 2, [1],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query62 *)
let HOQ_QUERY62 = slq_hist 62 (1536, 0, [0],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query63 *)
let HOQ_QUERY63 = slq_hist 63 (1536, 0, [1],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
