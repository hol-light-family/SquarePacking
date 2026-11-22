(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries032.lean                          *)
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

(* Lean: query1024 *)
let HOQ_QUERY1024 = slq_hist 1024 (8192, 1, [1; 2; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1025 *)
let HOQ_QUERY1025 = slq_hist 1025 (8192, 1, [0; 1; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1026 *)
let HOQ_QUERY1026 = slq_hist 1026 (8192, 1, [0; 2; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1027 *)
let HOQ_QUERY1027 = slq_hist 1027 (8192, 1, [1; 2; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1028 *)
let HOQ_QUERY1028 = slq_hist 1028 (8192, 1, [0; 3; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1029 *)
let HOQ_QUERY1029 = slq_hist 1029 (8192, 1, [1; 3; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1030 *)
let HOQ_QUERY1030 = slq_hist 1030 (8192, 1, [2; 3; 4],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1031 *)
let HOQ_QUERY1031 = slq_hist 1031 (8192, 1, [0; 1; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1032 *)
let HOQ_QUERY1032 = slq_hist 1032 (8192, 1, [1; 2; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1033 *)
let HOQ_QUERY1033 = slq_hist 1033 (8192, 1, [0; 3; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1034 *)
let HOQ_QUERY1034 = slq_hist 1034 (8192, 1, [1; 3; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1035 *)
let HOQ_QUERY1035 = slq_hist 1035 (8192, 1, [2; 3; 5],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1036 *)
let HOQ_QUERY1036 = slq_hist 1036 (8192, 1, [0; 4; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1037 *)
let HOQ_QUERY1037 = slq_hist 1037 (8192, 1, [1; 4; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1038 *)
let HOQ_QUERY1038 = slq_hist 1038 (8192, 1, [2; 4; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1039 *)
let HOQ_QUERY1039 = slq_hist 1039 (8192, 1, [3; 4; 5],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1040 *)
let HOQ_QUERY1040 = slq_hist 1040 (8192, 1, [0; 1; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1041 *)
let HOQ_QUERY1041 = slq_hist 1041 (8192, 1, [0; 2; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1042 *)
let HOQ_QUERY1042 = slq_hist 1042 (8192, 1, [1; 2; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1043 *)
let HOQ_QUERY1043 = slq_hist 1043 (8192, 1, [0; 3; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1044 *)
let HOQ_QUERY1044 = slq_hist 1044 (8192, 1, [1; 3; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1045 *)
let HOQ_QUERY1045 = slq_hist 1045 (8192, 1, [2; 3; 6],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1046 *)
let HOQ_QUERY1046 = slq_hist 1046 (8192, 1, [0; 4; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1047 *)
let HOQ_QUERY1047 = slq_hist 1047 (8192, 1, [1; 4; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1048 *)
let HOQ_QUERY1048 = slq_hist 1048 (8192, 1, [2; 4; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1049 *)
let HOQ_QUERY1049 = slq_hist 1049 (8192, 1, [3; 4; 6],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1050 *)
let HOQ_QUERY1050 = slq_hist 1050 (8192, 1, [0; 5; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1051 *)
let HOQ_QUERY1051 = slq_hist 1051 (8192, 1, [1; 5; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1052 *)
let HOQ_QUERY1052 = slq_hist 1052 (8192, 1, [2; 5; 6],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1053 *)
let HOQ_QUERY1053 = slq_hist 1053 (8192, 1, [3; 5; 6],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1054 *)
let HOQ_QUERY1054 = slq_hist 1054 (8192, 1, [4; 5; 6],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1055 *)
let HOQ_QUERY1055 = slq_hist 1055 (8192, 1, [0; 1; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
