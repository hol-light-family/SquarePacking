(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries027.lean                          *)
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

(* Lean: query864 *)
let HOQ_QUERY864 = slq_hist 864 (3072, 0, [8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query865 *)
let HOQ_QUERY865 = slq_hist 865 (3072, 0, [9],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query866 *)
let HOQ_QUERY866 = slq_hist 866 (3072, 1, [0],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query867 *)
let HOQ_QUERY867 = slq_hist 867 (3072, 1, [0; 1],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query868 *)
let HOQ_QUERY868 = slq_hist 868 (3072, 1, [2],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query869 *)
let HOQ_QUERY869 = slq_hist 869 (3072, 1, [0; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query870 *)
let HOQ_QUERY870 = slq_hist 870 (3072, 1, [1; 2],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query871 *)
let HOQ_QUERY871 = slq_hist 871 (3072, 1, [0; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query872 *)
let HOQ_QUERY872 = slq_hist 872 (3072, 1, [2; 3],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query873 *)
let HOQ_QUERY873 = slq_hist 873 (3072, 1, [0; 4],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query874 *)
let HOQ_QUERY874 = slq_hist 874 (3072, 1, [2; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query875 *)
let HOQ_QUERY875 = slq_hist 875 (3072, 1, [5],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query876 *)
let HOQ_QUERY876 = slq_hist 876 (3072, 1, [0; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query877 *)
let HOQ_QUERY877 = slq_hist 877 (3072, 1, [1; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query878 *)
let HOQ_QUERY878 = slq_hist 878 (3072, 1, [2; 5],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query879 *)
let HOQ_QUERY879 = slq_hist 879 (3072, 1, [3; 5],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query880 *)
let HOQ_QUERY880 = slq_hist 880 (3072, 1, [4; 5],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query881 *)
let HOQ_QUERY881 = slq_hist 881 (3072, 1, [0; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query882 *)
let HOQ_QUERY882 = slq_hist 882 (3072, 1, [2; 6],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query883 *)
let HOQ_QUERY883 = slq_hist 883 (3072, 1, [5; 6],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query884 *)
let HOQ_QUERY884 = slq_hist 884 (3072, 1, [0; 7],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query885 *)
let HOQ_QUERY885 = slq_hist 885 (3072, 1, [2; 7],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query886 *)
let HOQ_QUERY886 = slq_hist 886 (3072, 1, [5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query887 *)
let HOQ_QUERY887 = slq_hist 887 (3072, 1, [8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query888 *)
let HOQ_QUERY888 = slq_hist 888 (3072, 1, [0; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query889 *)
let HOQ_QUERY889 = slq_hist 889 (3072, 1, [1; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query890 *)
let HOQ_QUERY890 = slq_hist 890 (3072, 1, [2; 8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query891 *)
let HOQ_QUERY891 = slq_hist 891 (3072, 1, [3; 8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query892 *)
let HOQ_QUERY892 = slq_hist 892 (3072, 1, [4; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query893 *)
let HOQ_QUERY893 = slq_hist 893 (3072, 1, [5; 8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query894 *)
let HOQ_QUERY894 = slq_hist 894 (3072, 1, [6; 8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query895 *)
let HOQ_QUERY895 = slq_hist 895 (3072, 1, [7; 8],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
