(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries036.lean                          *)
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

(* Lean: query1152 *)
let HOQ_QUERY1152 = slq_hist 1152 (16384, 1, [2; 3; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1153 *)
let HOQ_QUERY1153 = slq_hist 1153 (16384, 1, [0; 1; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1154 *)
let HOQ_QUERY1154 = slq_hist 1154 (16384, 1, [0; 2; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1155 *)
let HOQ_QUERY1155 = slq_hist 1155 (16384, 1, [1; 2; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1156 *)
let HOQ_QUERY1156 = slq_hist 1156 (16384, 1, [0; 3; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1157 *)
let HOQ_QUERY1157 = slq_hist 1157 (16384, 1, [1; 3; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1158 *)
let HOQ_QUERY1158 = slq_hist 1158 (16384, 1, [2; 3; 5],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1159 *)
let HOQ_QUERY1159 = slq_hist 1159 (16384, 1, [0; 4; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1160 *)
let HOQ_QUERY1160 = slq_hist 1160 (16384, 1, [1; 4; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1161 *)
let HOQ_QUERY1161 = slq_hist 1161 (16384, 1, [2; 4; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1162 *)
let HOQ_QUERY1162 = slq_hist 1162 (16384, 1, [3; 4; 5],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1163 *)
let HOQ_QUERY1163 = slq_hist 1163 (16384, 1, [0; 1; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1164 *)
let HOQ_QUERY1164 = slq_hist 1164 (16384, 1, [0; 2; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1165 *)
let HOQ_QUERY1165 = slq_hist 1165 (16384, 1, [1; 2; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1166 *)
let HOQ_QUERY1166 = slq_hist 1166 (16384, 1, [0; 3; 6],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1167 *)
let HOQ_QUERY1167 = slq_hist 1167 (16384, 1, [1; 3; 6],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1168 *)
let HOQ_QUERY1168 = slq_hist 1168 (16384, 1, [2; 3; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1169 *)
let HOQ_QUERY1169 = slq_hist 1169 (16384, 1, [0; 4; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1170 *)
let HOQ_QUERY1170 = slq_hist 1170 (16384, 1, [1; 4; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1171 *)
let HOQ_QUERY1171 = slq_hist 1171 (16384, 1, [2; 4; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1172 *)
let HOQ_QUERY1172 = slq_hist 1172 (16384, 1, [3; 4; 6],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1173 *)
let HOQ_QUERY1173 = slq_hist 1173 (16384, 1, [0; 5; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1174 *)
let HOQ_QUERY1174 = slq_hist 1174 (16384, 1, [1; 5; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1175 *)
let HOQ_QUERY1175 = slq_hist 1175 (16384, 1, [2; 5; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1176 *)
let HOQ_QUERY1176 = slq_hist 1176 (16384, 1, [3; 5; 6],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1177 *)
let HOQ_QUERY1177 = slq_hist 1177 (16384, 1, [4; 5; 6],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1178 *)
let HOQ_QUERY1178 = slq_hist 1178 (16384, 1, [0; 1; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1179 *)
let HOQ_QUERY1179 = slq_hist 1179 (16384, 1, [0; 2; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1180 *)
let HOQ_QUERY1180 = slq_hist 1180 (16384, 1, [1; 2; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1181 *)
let HOQ_QUERY1181 = slq_hist 1181 (16384, 1, [0; 3; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1182 *)
let HOQ_QUERY1182 = slq_hist 1182 (16384, 1, [1; 3; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1183 *)
let HOQ_QUERY1183 = slq_hist 1183 (16384, 1, [2; 3; 7],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
