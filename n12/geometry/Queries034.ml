(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries034.lean                          *)
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

(* Lean: query1088 *)
let HOQ_QUERY1088 = slq_hist 1088 (8192, 1, [3; 5; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1089 *)
let HOQ_QUERY1089 = slq_hist 1089 (8192, 1, [4; 5; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1090 *)
let HOQ_QUERY1090 = slq_hist 1090 (8192, 1, [0; 6; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1091 *)
let HOQ_QUERY1091 = slq_hist 1091 (8192, 1, [1; 6; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1092 *)
let HOQ_QUERY1092 = slq_hist 1092 (8192, 1, [2; 6; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1093 *)
let HOQ_QUERY1093 = slq_hist 1093 (8192, 1, [3; 6; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1094 *)
let HOQ_QUERY1094 = slq_hist 1094 (8192, 1, [4; 6; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1095 *)
let HOQ_QUERY1095 = slq_hist 1095 (8192, 1, [5; 6; 8],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1096 *)
let HOQ_QUERY1096 = slq_hist 1096 (8192, 1, [0; 7; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1097 *)
let HOQ_QUERY1097 = slq_hist 1097 (8192, 1, [1; 7; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1098 *)
let HOQ_QUERY1098 = slq_hist 1098 (8192, 1, [2; 7; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1099 *)
let HOQ_QUERY1099 = slq_hist 1099 (8192, 1, [3; 7; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1100 *)
let HOQ_QUERY1100 = slq_hist 1100 (8192, 1, [4; 7; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1101 *)
let HOQ_QUERY1101 = slq_hist 1101 (8192, 1, [5; 7; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1102 *)
let HOQ_QUERY1102 = slq_hist 1102 (8192, 1, [6; 7; 8],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1103 *)
let HOQ_QUERY1103 = slq_hist 1103 (8192, 1, [0; 1; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1104 *)
let HOQ_QUERY1104 = slq_hist 1104 (8192, 1, [0; 2; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1105 *)
let HOQ_QUERY1105 = slq_hist 1105 (8192, 1, [1; 2; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1106 *)
let HOQ_QUERY1106 = slq_hist 1106 (8192, 1, [0; 3; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1107 *)
let HOQ_QUERY1107 = slq_hist 1107 (8192, 1, [1; 3; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1108 *)
let HOQ_QUERY1108 = slq_hist 1108 (8192, 1, [2; 3; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1109 *)
let HOQ_QUERY1109 = slq_hist 1109 (8192, 1, [0; 4; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1110 *)
let HOQ_QUERY1110 = slq_hist 1110 (8192, 1, [1; 4; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1111 *)
let HOQ_QUERY1111 = slq_hist 1111 (8192, 1, [2; 4; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1112 *)
let HOQ_QUERY1112 = slq_hist 1112 (8192, 1, [3; 4; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1113 *)
let HOQ_QUERY1113 = slq_hist 1113 (8192, 1, [0; 5; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1114 *)
let HOQ_QUERY1114 = slq_hist 1114 (8192, 1, [1; 5; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1115 *)
let HOQ_QUERY1115 = slq_hist 1115 (8192, 1, [2; 5; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1116 *)
let HOQ_QUERY1116 = slq_hist 1116 (8192, 1, [3; 5; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1117 *)
let HOQ_QUERY1117 = slq_hist 1117 (8192, 1, [4; 5; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1118 *)
let HOQ_QUERY1118 = slq_hist 1118 (8192, 1, [0; 6; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1119 *)
let HOQ_QUERY1119 = slq_hist 1119 (8192, 1, [1; 6; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
