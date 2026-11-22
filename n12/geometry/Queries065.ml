(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries065.lean *)
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

(* Lean: query2080 *)
let HOQ_QUERY2080 = slq_hist 2080 (512, 2, [4; 9; 15; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query2081 *)
let HOQ_QUERY2081 = slq_hist 2081 (512, 2, [4; 9; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query2082 *)
let HOQ_QUERY2082 = slq_hist 2082 (512, 2, [8; 9; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2083 *)
let HOQ_QUERY2083 = slq_hist 2083 (512, 2, [8; 9; 12; 13; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2084 *)
let HOQ_QUERY2084 = slq_hist 2084 (512, 2, [8; 9; 12; 15; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2085 *)
let HOQ_QUERY2085 = slq_hist 2085 (512, 2, [8; 9; 13; 15; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2086 *)
let HOQ_QUERY2086 = slq_hist 2086 (512, 2, [8; 9; 12; 15; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2087 *)
let HOQ_QUERY2087 = slq_hist 2087 (512, 2, [8; 9; 13; 15; 18],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2088 *)
let HOQ_QUERY2088 = slq_hist 2088 (512, 2, [8; 9; 12; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2089 *)
let HOQ_QUERY2089 = slq_hist 2089 (512, 2, [8; 9; 13; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2090 *)
let HOQ_QUERY2090 = slq_hist 2090 (3072, 0, [0; 1],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2091 *)
let HOQ_QUERY2091 = slq_hist 2091 (3072, 0, [0; 2],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2092 *)
let HOQ_QUERY2092 = slq_hist 2092 (3072, 0, [1; 2],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2093 *)
let HOQ_QUERY2093 = slq_hist 2093 (3072, 0, [0; 3],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2094 *)
let HOQ_QUERY2094 = slq_hist 2094 (3072, 0, [1; 3],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2095 *)
let HOQ_QUERY2095 = slq_hist 2095 (3072, 0, [2; 3],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2096 *)
let HOQ_QUERY2096 = slq_hist 2096 (3072, 0, [0; 4],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2097 *)
let HOQ_QUERY2097 = slq_hist 2097 (3072, 0, [1; 4],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2098 *)
let HOQ_QUERY2098 = slq_hist 2098 (3072, 0, [2; 4],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2099 *)
let HOQ_QUERY2099 = slq_hist 2099 (3072, 0, [3; 4],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2100 *)
let HOQ_QUERY2100 = slq_hist 2100 (3072, 0, [2; 5],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2101 *)
let HOQ_QUERY2101 = slq_hist 2101 (3072, 0, [0; 6],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2102 *)
let HOQ_QUERY2102 = slq_hist 2102 (3072, 0, [1; 6],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2103 *)
let HOQ_QUERY2103 = slq_hist 2103 (3072, 0, [2; 6],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2104 *)
let HOQ_QUERY2104 = slq_hist 2104 (3072, 0, [3; 6],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2105 *)
let HOQ_QUERY2105 = slq_hist 2105 (3072, 0, [4; 6],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2106 *)
let HOQ_QUERY2106 = slq_hist 2106 (3072, 0, [5; 6],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2107 *)
let HOQ_QUERY2107 = slq_hist 2107 (3072, 0, [0; 7],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2108 *)
let HOQ_QUERY2108 = slq_hist 2108 (3072, 0, [1; 7],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2109 *)
let HOQ_QUERY2109 = slq_hist 2109 (3072, 0, [2; 7],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2110 *)
let HOQ_QUERY2110 = slq_hist 2110 (3072, 0, [3; 7],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2111 *)
let HOQ_QUERY2111 = slq_hist 2111 (3072, 0, [4; 7],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
