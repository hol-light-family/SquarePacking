(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries066.lean *)
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

(* Lean: query2112 *)
let HOQ_QUERY2112 = slq_hist 2112 (3072, 0, [6; 7],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2113 *)
let HOQ_QUERY2113 = slq_hist 2113 (3072, 0, [0; 8],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2114 *)
let HOQ_QUERY2114 = slq_hist 2114 (3072, 0, [1; 8],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2115 *)
let HOQ_QUERY2115 = slq_hist 2115 (3072, 0, [2; 8],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2116 *)
let HOQ_QUERY2116 = slq_hist 2116 (3072, 0, [3; 8],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2117 *)
let HOQ_QUERY2117 = slq_hist 2117 (3072, 0, [4; 8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2118 *)
let HOQ_QUERY2118 = slq_hist 2118 (3072, 0, [6; 8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2119 *)
let HOQ_QUERY2119 = slq_hist 2119 (3072, 0, [7; 8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2120 *)
let HOQ_QUERY2120 = slq_hist 2120 (3072, 0, [0; 9],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2121 *)
let HOQ_QUERY2121 = slq_hist 2121 (3072, 0, [1; 9],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2122 *)
let HOQ_QUERY2122 = slq_hist 2122 (3072, 0, [2; 9],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2123 *)
let HOQ_QUERY2123 = slq_hist 2123 (3072, 0, [3; 9],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2124 *)
let HOQ_QUERY2124 = slq_hist 2124 (3072, 0, [4; 9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2125 *)
let HOQ_QUERY2125 = slq_hist 2125 (3072, 0, [6; 9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2126 *)
let HOQ_QUERY2126 = slq_hist 2126 (3072, 0, [7; 9],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2127 *)
let HOQ_QUERY2127 = slq_hist 2127 (3072, 0, [8; 9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query2128 *)
let HOQ_QUERY2128 = slq_hist 2128 (3072, 2, [0; 5],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2129 *)
let HOQ_QUERY2129 = slq_hist 2129 (3072, 2, [0; 5; 11],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query2130 *)
let HOQ_QUERY2130 = slq_hist 2130 (3072, 2, [0; 5; 11; 13],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query2131 *)
let HOQ_QUERY2131 = slq_hist 2131 (3072, 2, [0; 5; 14],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2132 *)
let HOQ_QUERY2132 = slq_hist 2132 (3072, 2, [0; 5; 11; 14],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query2133 *)
let HOQ_QUERY2133 = slq_hist 2133 (3072, 2, [0; 5; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2134 *)
let HOQ_QUERY2134 = slq_hist 2134 (3072, 2, [0; 5; 11; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query2135 *)
let HOQ_QUERY2135 = slq_hist 2135 (3072, 2, [0; 5; 14; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2136 *)
let HOQ_QUERY2136 = slq_hist 2136 (3072, 2, [0; 5; 17],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2137 *)
let HOQ_QUERY2137 = slq_hist 2137 (3072, 2, [0; 5; 11; 17],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query2138 *)
let HOQ_QUERY2138 = slq_hist 2138 (3072, 2, [0; 5; 14; 17],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2139 *)
let HOQ_QUERY2139 = slq_hist 2139 (3072, 2, [0; 5; 16; 17],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2140 *)
let HOQ_QUERY2140 = slq_hist 2140 (3072, 2, [0; 5; 19],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2141 *)
let HOQ_QUERY2141 = slq_hist 2141 (3072, 2, [0; 5; 11; 19],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query2142 *)
let HOQ_QUERY2142 = slq_hist 2142 (3072, 2, [0; 5; 14; 19],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2143 *)
let HOQ_QUERY2143 = slq_hist 2143 (3072, 2, [0; 5; 16; 19],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
