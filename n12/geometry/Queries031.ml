(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries031.lean                          *)
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

(* Lean: query992 *)
let HOQ_QUERY992 = slq_hist 992 (4096, 1, [3; 4; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query993 *)
let HOQ_QUERY993 = slq_hist 993 (4096, 1, [0; 5; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query994 *)
let HOQ_QUERY994 = slq_hist 994 (4096, 1, [1; 5; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query995 *)
let HOQ_QUERY995 = slq_hist 995 (4096, 1, [2; 5; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query996 *)
let HOQ_QUERY996 = slq_hist 996 (4096, 1, [3; 5; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query997 *)
let HOQ_QUERY997 = slq_hist 997 (4096, 1, [4; 5; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query998 *)
let HOQ_QUERY998 = slq_hist 998 (4096, 1, [0; 6; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query999 *)
let HOQ_QUERY999 = slq_hist 999 (4096, 1, [1; 6; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1000 *)
let HOQ_QUERY1000 = slq_hist 1000 (4096, 1, [2; 6; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1001 *)
let HOQ_QUERY1001 = slq_hist 1001 (4096, 1, [3; 6; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1002 *)
let HOQ_QUERY1002 = slq_hist 1002 (4096, 1, [4; 6; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1003 *)
let HOQ_QUERY1003 = slq_hist 1003 (4096, 1, [5; 6; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1004 *)
let HOQ_QUERY1004 = slq_hist 1004 (4096, 1, [0; 7; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1005 *)
let HOQ_QUERY1005 = slq_hist 1005 (4096, 1, [1; 7; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1006 *)
let HOQ_QUERY1006 = slq_hist 1006 (4096, 1, [2; 7; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1007 *)
let HOQ_QUERY1007 = slq_hist 1007 (4096, 1, [3; 7; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1008 *)
let HOQ_QUERY1008 = slq_hist 1008 (4096, 1, [4; 7; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1009 *)
let HOQ_QUERY1009 = slq_hist 1009 (4096, 1, [5; 7; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1010 *)
let HOQ_QUERY1010 = slq_hist 1010 (4096, 1, [6; 7; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1011 *)
let HOQ_QUERY1011 = slq_hist 1011 (4096, 1, [0; 8; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1012 *)
let HOQ_QUERY1012 = slq_hist 1012 (4096, 1, [1; 8; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1013 *)
let HOQ_QUERY1013 = slq_hist 1013 (4096, 1, [2; 8; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1014 *)
let HOQ_QUERY1014 = slq_hist 1014 (4096, 1, [3; 8; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1015 *)
let HOQ_QUERY1015 = slq_hist 1015 (4096, 1, [4; 8; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1016 *)
let HOQ_QUERY1016 = slq_hist 1016 (4096, 1, [5; 8; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1017 *)
let HOQ_QUERY1017 = slq_hist 1017 (4096, 1, [6; 8; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1018 *)
let HOQ_QUERY1018 = slq_hist 1018 (4096, 1, [7; 8; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1019 *)
let HOQ_QUERY1019 = slq_hist 1019 (4096, 2, [0; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query1020 *)
let HOQ_QUERY1020 = slq_hist 1020 (4096, 2, [1; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1021 *)
let HOQ_QUERY1021 = slq_hist 1021 (8192, 1, [0; 1; 2],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1022 *)
let HOQ_QUERY1022 = slq_hist 1022 (8192, 1, [0; 1; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1023 *)
let HOQ_QUERY1023 = slq_hist 1023 (8192, 1, [0; 2; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
