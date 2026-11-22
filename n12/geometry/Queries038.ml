(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries038.lean                          *)
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

(* Lean: query1216 *)
let HOQ_QUERY1216 = slq_hist 1216 (16384, 1, [2; 6; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1217 *)
let HOQ_QUERY1217 = slq_hist 1217 (16384, 1, [3; 6; 8],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1218 *)
let HOQ_QUERY1218 = slq_hist 1218 (16384, 1, [4; 6; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1219 *)
let HOQ_QUERY1219 = slq_hist 1219 (16384, 1, [5; 6; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1220 *)
let HOQ_QUERY1220 = slq_hist 1220 (16384, 1, [0; 7; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1221 *)
let HOQ_QUERY1221 = slq_hist 1221 (16384, 1, [1; 7; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1222 *)
let HOQ_QUERY1222 = slq_hist 1222 (16384, 1, [2; 7; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1223 *)
let HOQ_QUERY1223 = slq_hist 1223 (16384, 1, [3; 7; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1224 *)
let HOQ_QUERY1224 = slq_hist 1224 (16384, 1, [4; 7; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1225 *)
let HOQ_QUERY1225 = slq_hist 1225 (16384, 1, [5; 7; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1226 *)
let HOQ_QUERY1226 = slq_hist 1226 (16384, 1, [6; 7; 8],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1227 *)
let HOQ_QUERY1227 = slq_hist 1227 (16384, 1, [0; 1; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1228 *)
let HOQ_QUERY1228 = slq_hist 1228 (16384, 1, [0; 2; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1229 *)
let HOQ_QUERY1229 = slq_hist 1229 (16384, 1, [1; 2; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1230 *)
let HOQ_QUERY1230 = slq_hist 1230 (16384, 1, [0; 3; 9],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1231 *)
let HOQ_QUERY1231 = slq_hist 1231 (16384, 1, [1; 3; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1232 *)
let HOQ_QUERY1232 = slq_hist 1232 (16384, 1, [2; 3; 9],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1233 *)
let HOQ_QUERY1233 = slq_hist 1233 (16384, 1, [0; 4; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1234 *)
let HOQ_QUERY1234 = slq_hist 1234 (16384, 1, [1; 4; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1235 *)
let HOQ_QUERY1235 = slq_hist 1235 (16384, 1, [2; 4; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1236 *)
let HOQ_QUERY1236 = slq_hist 1236 (16384, 1, [3; 4; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1237 *)
let HOQ_QUERY1237 = slq_hist 1237 (16384, 1, [0; 5; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1238 *)
let HOQ_QUERY1238 = slq_hist 1238 (16384, 1, [1; 5; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1239 *)
let HOQ_QUERY1239 = slq_hist 1239 (16384, 1, [2; 5; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1240 *)
let HOQ_QUERY1240 = slq_hist 1240 (16384, 1, [3; 5; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1241 *)
let HOQ_QUERY1241 = slq_hist 1241 (16384, 1, [4; 5; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1242 *)
let HOQ_QUERY1242 = slq_hist 1242 (16384, 1, [0; 6; 9],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1243 *)
let HOQ_QUERY1243 = slq_hist 1243 (16384, 1, [1; 6; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1244 *)
let HOQ_QUERY1244 = slq_hist 1244 (16384, 1, [2; 6; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1245 *)
let HOQ_QUERY1245 = slq_hist 1245 (16384, 1, [3; 6; 9],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1246 *)
let HOQ_QUERY1246 = slq_hist 1246 (16384, 1, [4; 6; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1247 *)
let HOQ_QUERY1247 = slq_hist 1247 (16384, 1, [5; 6; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
