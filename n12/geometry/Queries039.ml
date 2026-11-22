(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries039.lean                          *)
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

(* Lean: query1248 *)
let HOQ_QUERY1248 = slq_hist 1248 (16384, 1, [0; 7; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1249 *)
let HOQ_QUERY1249 = slq_hist 1249 (16384, 1, [1; 7; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1250 *)
let HOQ_QUERY1250 = slq_hist 1250 (16384, 1, [2; 7; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1251 *)
let HOQ_QUERY1251 = slq_hist 1251 (16384, 1, [3; 7; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1252 *)
let HOQ_QUERY1252 = slq_hist 1252 (16384, 1, [4; 7; 9],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1253 *)
let HOQ_QUERY1253 = slq_hist 1253 (16384, 1, [5; 7; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1254 *)
let HOQ_QUERY1254 = slq_hist 1254 (16384, 1, [6; 7; 9],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1255 *)
let HOQ_QUERY1255 = slq_hist 1255 (16384, 1, [0; 8; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1256 *)
let HOQ_QUERY1256 = slq_hist 1256 (16384, 1, [1; 8; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1257 *)
let HOQ_QUERY1257 = slq_hist 1257 (16384, 1, [2; 8; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1258 *)
let HOQ_QUERY1258 = slq_hist 1258 (16384, 1, [3; 8; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1259 *)
let HOQ_QUERY1259 = slq_hist 1259 (16384, 1, [4; 8; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1260 *)
let HOQ_QUERY1260 = slq_hist 1260 (16384, 1, [5; 8; 9],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1261 *)
let HOQ_QUERY1261 = slq_hist 1261 (16384, 1, [7; 8; 9],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1262 *)
let HOQ_QUERY1262 = slq_hist 1262 (16384, 2, [8; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query1263 *)
let HOQ_QUERY1263 = slq_hist 1263 (16384, 2, [9; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query1264 *)
let HOQ_QUERY1264 = slq_hist 1264 (32768, 1, [0; 1; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1265 *)
let HOQ_QUERY1265 = slq_hist 1265 (32768, 1, [0; 1; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1266 *)
let HOQ_QUERY1266 = slq_hist 1266 (32768, 1, [0; 2; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1267 *)
let HOQ_QUERY1267 = slq_hist 1267 (32768, 1, [1; 2; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1268 *)
let HOQ_QUERY1268 = slq_hist 1268 (32768, 1, [0; 1; 4],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1269 *)
let HOQ_QUERY1269 = slq_hist 1269 (32768, 1, [0; 2; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1270 *)
let HOQ_QUERY1270 = slq_hist 1270 (32768, 1, [1; 2; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1271 *)
let HOQ_QUERY1271 = slq_hist 1271 (32768, 1, [0; 3; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1272 *)
let HOQ_QUERY1272 = slq_hist 1272 (32768, 1, [1; 3; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1273 *)
let HOQ_QUERY1273 = slq_hist 1273 (32768, 1, [2; 3; 4],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1274 *)
let HOQ_QUERY1274 = slq_hist 1274 (32768, 1, [0; 1; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1275 *)
let HOQ_QUERY1275 = slq_hist 1275 (32768, 1, [0; 2; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1276 *)
let HOQ_QUERY1276 = slq_hist 1276 (32768, 1, [1; 2; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1277 *)
let HOQ_QUERY1277 = slq_hist 1277 (32768, 1, [0; 3; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1278 *)
let HOQ_QUERY1278 = slq_hist 1278 (32768, 1, [1; 3; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1279 *)
let HOQ_QUERY1279 = slq_hist 1279 (32768, 1, [2; 3; 5],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
