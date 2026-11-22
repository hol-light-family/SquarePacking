(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries067.lean *)
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

(* Lean: query2144 *)
let HOQ_QUERY2144 = slq_hist 2144 (3072, 2, [0; 5; 17; 19],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2145 *)
let HOQ_QUERY2145 = slq_hist 2145 (3072, 2, [3; 5; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query2146 *)
let HOQ_QUERY2146 = slq_hist 2146 (3072, 2, [3; 5; 11; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query2147 *)
let HOQ_QUERY2147 = slq_hist 2147 (3072, 2, [3; 5; 13; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query2148 *)
let HOQ_QUERY2148 = slq_hist 2148 (3072, 2, [3; 5; 16; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query2149 *)
let HOQ_QUERY2149 = slq_hist 2149 (3072, 2, [3; 5; 17; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query2150 *)
let HOQ_QUERY2150 = slq_hist 2150 (3072, 2, [4; 5; 11],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2151 *)
let HOQ_QUERY2151 = slq_hist 2151 (3072, 2, [4; 5; 11; 14],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2152 *)
let HOQ_QUERY2152 = slq_hist 2152 (3072, 2, [4; 5; 11; 16],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2153 *)
let HOQ_QUERY2153 = slq_hist 2153 (3072, 2, [4; 5; 11; 17],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2154 *)
let HOQ_QUERY2154 = slq_hist 2154 (3072, 2, [4; 5; 19],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2155 *)
let HOQ_QUERY2155 = slq_hist 2155 (3072, 2, [4; 5; 11; 19],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query2156 *)
let HOQ_QUERY2156 = slq_hist 2156 (3072, 2, [4; 5; 13; 19],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2157 *)
let HOQ_QUERY2157 = slq_hist 2157 (3072, 2, [4; 5; 14; 19],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2158 *)
let HOQ_QUERY2158 = slq_hist 2158 (3072, 2, [4; 5; 17; 19],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2159 *)
let HOQ_QUERY2159 = slq_hist 2159 (3072, 2, [5; 7; 14],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query2160 *)
let HOQ_QUERY2160 = slq_hist 2160 (3072, 2, [5; 7; 11; 14],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query2161 *)
let HOQ_QUERY2161 = slq_hist 2161 (3072, 2, [5; 7; 13; 14],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query2162 *)
let HOQ_QUERY2162 = slq_hist 2162 (3072, 2, [5; 7; 14; 16],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query2163 *)
let HOQ_QUERY2163 = slq_hist 2163 (3072, 2, [5; 7; 14; 19],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query2164 *)
let HOQ_QUERY2164 = slq_hist 2164 (3072, 2, [5; 8],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2165 *)
let HOQ_QUERY2165 = slq_hist 2165 (3072, 2, [5; 8; 11],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2166 *)
let HOQ_QUERY2166 = slq_hist 2166 (3072, 2, [5; 8; 13],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2167 *)
let HOQ_QUERY2167 = slq_hist 2167 (3072, 2, [5; 8; 11; 13],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2168 *)
let HOQ_QUERY2168 = slq_hist 2168 (3072, 2, [5; 8; 14],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2169 *)
let HOQ_QUERY2169 = slq_hist 2169 (3072, 2, [5; 8; 11; 14],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2170 *)
let HOQ_QUERY2170 = slq_hist 2170 (3072, 2, [5; 8; 13; 14],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2171 *)
let HOQ_QUERY2171 = slq_hist 2171 (3072, 2, [5; 8; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2172 *)
let HOQ_QUERY2172 = slq_hist 2172 (3072, 2, [5; 8; 11; 17],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2173 *)
let HOQ_QUERY2173 = slq_hist 2173 (3072, 2, [5; 8; 13; 17],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2174 *)
let HOQ_QUERY2174 = slq_hist 2174 (3072, 2, [5; 8; 14; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2175 *)
let HOQ_QUERY2175 = slq_hist 2175 (3072, 2, [5; 8; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
