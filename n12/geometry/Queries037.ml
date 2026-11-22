(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries037.lean                          *)
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

(* Lean: query1184 *)
let HOQ_QUERY1184 = slq_hist 1184 (16384, 1, [0; 4; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1185 *)
let HOQ_QUERY1185 = slq_hist 1185 (16384, 1, [1; 4; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1186 *)
let HOQ_QUERY1186 = slq_hist 1186 (16384, 1, [2; 4; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1187 *)
let HOQ_QUERY1187 = slq_hist 1187 (16384, 1, [3; 4; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1188 *)
let HOQ_QUERY1188 = slq_hist 1188 (16384, 1, [0; 5; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1189 *)
let HOQ_QUERY1189 = slq_hist 1189 (16384, 1, [1; 5; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1190 *)
let HOQ_QUERY1190 = slq_hist 1190 (16384, 1, [2; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1191 *)
let HOQ_QUERY1191 = slq_hist 1191 (16384, 1, [3; 5; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1192 *)
let HOQ_QUERY1192 = slq_hist 1192 (16384, 1, [4; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1193 *)
let HOQ_QUERY1193 = slq_hist 1193 (16384, 1, [0; 6; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1194 *)
let HOQ_QUERY1194 = slq_hist 1194 (16384, 1, [1; 6; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1195 *)
let HOQ_QUERY1195 = slq_hist 1195 (16384, 1, [2; 6; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1196 *)
let HOQ_QUERY1196 = slq_hist 1196 (16384, 1, [3; 6; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1197 *)
let HOQ_QUERY1197 = slq_hist 1197 (16384, 1, [4; 6; 7],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1198 *)
let HOQ_QUERY1198 = slq_hist 1198 (16384, 1, [5; 6; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1199 *)
let HOQ_QUERY1199 = slq_hist 1199 (16384, 1, [0; 1; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1200 *)
let HOQ_QUERY1200 = slq_hist 1200 (16384, 1, [0; 2; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1201 *)
let HOQ_QUERY1201 = slq_hist 1201 (16384, 1, [1; 2; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1202 *)
let HOQ_QUERY1202 = slq_hist 1202 (16384, 1, [0; 3; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1203 *)
let HOQ_QUERY1203 = slq_hist 1203 (16384, 1, [1; 3; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1204 *)
let HOQ_QUERY1204 = slq_hist 1204 (16384, 1, [2; 3; 8],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1205 *)
let HOQ_QUERY1205 = slq_hist 1205 (16384, 1, [0; 4; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1206 *)
let HOQ_QUERY1206 = slq_hist 1206 (16384, 1, [1; 4; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1207 *)
let HOQ_QUERY1207 = slq_hist 1207 (16384, 1, [2; 4; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1208 *)
let HOQ_QUERY1208 = slq_hist 1208 (16384, 1, [3; 4; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1209 *)
let HOQ_QUERY1209 = slq_hist 1209 (16384, 1, [0; 5; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1210 *)
let HOQ_QUERY1210 = slq_hist 1210 (16384, 1, [1; 5; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1211 *)
let HOQ_QUERY1211 = slq_hist 1211 (16384, 1, [2; 5; 8],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1212 *)
let HOQ_QUERY1212 = slq_hist 1212 (16384, 1, [3; 5; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1213 *)
let HOQ_QUERY1213 = slq_hist 1213 (16384, 1, [4; 5; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1214 *)
let HOQ_QUERY1214 = slq_hist 1214 (16384, 1, [0; 6; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1215 *)
let HOQ_QUERY1215 = slq_hist 1215 (16384, 1, [1; 6; 8],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
