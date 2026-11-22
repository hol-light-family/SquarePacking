(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries035.lean                          *)
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

(* Lean: query1120 *)
let HOQ_QUERY1120 = slq_hist 1120 (8192, 1, [2; 6; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1121 *)
let HOQ_QUERY1121 = slq_hist 1121 (8192, 1, [3; 6; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1122 *)
let HOQ_QUERY1122 = slq_hist 1122 (8192, 1, [4; 6; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1123 *)
let HOQ_QUERY1123 = slq_hist 1123 (8192, 1, [5; 6; 9],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1124 *)
let HOQ_QUERY1124 = slq_hist 1124 (8192, 1, [0; 7; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1125 *)
let HOQ_QUERY1125 = slq_hist 1125 (8192, 1, [1; 7; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1126 *)
let HOQ_QUERY1126 = slq_hist 1126 (8192, 1, [2; 7; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1127 *)
let HOQ_QUERY1127 = slq_hist 1127 (8192, 1, [3; 7; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1128 *)
let HOQ_QUERY1128 = slq_hist 1128 (8192, 1, [4; 7; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1129 *)
let HOQ_QUERY1129 = slq_hist 1129 (8192, 1, [5; 7; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1130 *)
let HOQ_QUERY1130 = slq_hist 1130 (8192, 1, [6; 7; 9],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1131 *)
let HOQ_QUERY1131 = slq_hist 1131 (8192, 1, [0; 8; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1132 *)
let HOQ_QUERY1132 = slq_hist 1132 (8192, 1, [1; 8; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1133 *)
let HOQ_QUERY1133 = slq_hist 1133 (8192, 1, [2; 8; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1134 *)
let HOQ_QUERY1134 = slq_hist 1134 (8192, 1, [3; 8; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1135 *)
let HOQ_QUERY1135 = slq_hist 1135 (8192, 1, [4; 8; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1136 *)
let HOQ_QUERY1136 = slq_hist 1136 (8192, 1, [5; 8; 9],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1137 *)
let HOQ_QUERY1137 = slq_hist 1137 (8192, 1, [6; 8; 9],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1138 *)
let HOQ_QUERY1138 = slq_hist 1138 (8192, 1, [7; 8; 9],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1139 *)
let HOQ_QUERY1139 = slq_hist 1139 (8192, 2, [2; 12; 15; 18],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1140 *)
let HOQ_QUERY1140 = slq_hist 1140 (8192, 2, [4; 10; 12; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1141 *)
let HOQ_QUERY1141 = slq_hist 1141 (8192, 2, [4; 12; 15; 18],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1142 *)
let HOQ_QUERY1142 = slq_hist 1142 (8192, 2, [6; 10; 12; 15],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1143 *)
let HOQ_QUERY1143 = slq_hist 1143 (16384, 1, [0; 1; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1144 *)
let HOQ_QUERY1144 = slq_hist 1144 (16384, 1, [0; 1; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1145 *)
let HOQ_QUERY1145 = slq_hist 1145 (16384, 1, [0; 2; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1146 *)
let HOQ_QUERY1146 = slq_hist 1146 (16384, 1, [1; 2; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1147 *)
let HOQ_QUERY1147 = slq_hist 1147 (16384, 1, [0; 1; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1148 *)
let HOQ_QUERY1148 = slq_hist 1148 (16384, 1, [0; 2; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1149 *)
let HOQ_QUERY1149 = slq_hist 1149 (16384, 1, [1; 2; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1150 *)
let HOQ_QUERY1150 = slq_hist 1150 (16384, 1, [0; 3; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1151 *)
let HOQ_QUERY1151 = slq_hist 1151 (16384, 1, [1; 3; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
