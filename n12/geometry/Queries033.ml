(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries033.lean                          *)
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

(* Lean: query1056 *)
let HOQ_QUERY1056 = slq_hist 1056 (8192, 1, [0; 2; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1057 *)
let HOQ_QUERY1057 = slq_hist 1057 (8192, 1, [1; 2; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1058 *)
let HOQ_QUERY1058 = slq_hist 1058 (8192, 1, [0; 3; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1059 *)
let HOQ_QUERY1059 = slq_hist 1059 (8192, 1, [1; 3; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1060 *)
let HOQ_QUERY1060 = slq_hist 1060 (8192, 1, [2; 3; 7],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1061 *)
let HOQ_QUERY1061 = slq_hist 1061 (8192, 1, [0; 4; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1062 *)
let HOQ_QUERY1062 = slq_hist 1062 (8192, 1, [1; 4; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1063 *)
let HOQ_QUERY1063 = slq_hist 1063 (8192, 1, [2; 4; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1064 *)
let HOQ_QUERY1064 = slq_hist 1064 (8192, 1, [3; 4; 7],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1065 *)
let HOQ_QUERY1065 = slq_hist 1065 (8192, 1, [0; 5; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1066 *)
let HOQ_QUERY1066 = slq_hist 1066 (8192, 1, [1; 5; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1067 *)
let HOQ_QUERY1067 = slq_hist 1067 (8192, 1, [2; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1068 *)
let HOQ_QUERY1068 = slq_hist 1068 (8192, 1, [3; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1069 *)
let HOQ_QUERY1069 = slq_hist 1069 (8192, 1, [4; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1070 *)
let HOQ_QUERY1070 = slq_hist 1070 (8192, 1, [0; 6; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1071 *)
let HOQ_QUERY1071 = slq_hist 1071 (8192, 1, [1; 6; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1072 *)
let HOQ_QUERY1072 = slq_hist 1072 (8192, 1, [2; 6; 7],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1073 *)
let HOQ_QUERY1073 = slq_hist 1073 (8192, 1, [3; 6; 7],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1074 *)
let HOQ_QUERY1074 = slq_hist 1074 (8192, 1, [4; 6; 7],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1075 *)
let HOQ_QUERY1075 = slq_hist 1075 (8192, 1, [5; 6; 7],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1076 *)
let HOQ_QUERY1076 = slq_hist 1076 (8192, 1, [0; 1; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1077 *)
let HOQ_QUERY1077 = slq_hist 1077 (8192, 1, [0; 2; 8],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1078 *)
let HOQ_QUERY1078 = slq_hist 1078 (8192, 1, [1; 2; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1079 *)
let HOQ_QUERY1079 = slq_hist 1079 (8192, 1, [0; 3; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1080 *)
let HOQ_QUERY1080 = slq_hist 1080 (8192, 1, [1; 3; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1081 *)
let HOQ_QUERY1081 = slq_hist 1081 (8192, 1, [2; 3; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1082 *)
let HOQ_QUERY1082 = slq_hist 1082 (8192, 1, [0; 4; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1083 *)
let HOQ_QUERY1083 = slq_hist 1083 (8192, 1, [1; 4; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1084 *)
let HOQ_QUERY1084 = slq_hist 1084 (8192, 1, [2; 4; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1085 *)
let HOQ_QUERY1085 = slq_hist 1085 (8192, 1, [3; 4; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1086 *)
let HOQ_QUERY1086 = slq_hist 1086 (8192, 1, [0; 5; 8],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1087 *)
let HOQ_QUERY1087 = slq_hist 1087 (8192, 1, [1; 5; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
