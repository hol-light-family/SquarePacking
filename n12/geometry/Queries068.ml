(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries068.lean *)
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

(* Lean: query2176 *)
let HOQ_QUERY2176 = slq_hist 2176 (3072, 2, [5; 8; 11; 19],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2177 *)
let HOQ_QUERY2177 = slq_hist 2177 (3072, 2, [5; 8; 13; 19],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2178 *)
let HOQ_QUERY2178 = slq_hist 2178 (3072, 2, [5; 8; 14; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query2179 *)
let HOQ_QUERY2179 = slq_hist 2179 (3072, 2, [5; 8; 16; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query2180 *)
let HOQ_QUERY2180 = slq_hist 2180 (3072, 2, [5; 8; 17; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query2181 *)
let HOQ_QUERY2181 = slq_hist 2181 (4096, 2, [0; 2; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query2182 *)
let HOQ_QUERY2182 = slq_hist 2182 (4096, 2, [1; 3; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query2183 *)
let HOQ_QUERY2183 = slq_hist 2183 (8192, 2, [2; 4; 10; 12; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2184 *)
let HOQ_QUERY2184 = slq_hist 2184 (8192, 2, [2; 4; 12; 15; 18],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query2185 *)
let HOQ_QUERY2185 = slq_hist 2185 (8192, 2, [4; 6; 10; 12; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2186 *)
let HOQ_QUERY2186 = slq_hist 2186 (8192, 2, [4; 6; 12; 15; 18],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query2187 *)
let HOQ_QUERY2187 = slq_hist 2187 (16384, 2, [6; 8; 16; 18; 19],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query2188 *)
let HOQ_QUERY2188 = slq_hist 2188 (16384, 2, [7; 9; 16; 18; 19],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query2189 *)
let HOQ_QUERY2189 = slq_hist 2189 (32768, 2, [3; 5; 11; 14; 17],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query2190 *)
let HOQ_QUERY2190 = slq_hist 2190 (32768, 2, [3; 5; 14; 17; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query2191 *)
let HOQ_QUERY2191 = slq_hist 2191 (32768, 2, [5; 7; 11; 14; 17],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query2192 *)
let HOQ_QUERY2192 = slq_hist 2192 (32768, 2, [5; 7; 14; 17; 19],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
