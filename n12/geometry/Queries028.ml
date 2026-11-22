(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries028.lean                          *)
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

(* Lean: query896 *)
let HOQ_QUERY896 = slq_hist 896 (3072, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query897 *)
let HOQ_QUERY897 = slq_hist 897 (3072, 1, [2; 9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query898 *)
let HOQ_QUERY898 = slq_hist 898 (3072, 1, [5; 9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query899 *)
let HOQ_QUERY899 = slq_hist 899 (3072, 1, [8; 9],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query900 *)
let HOQ_QUERY900 = slq_hist 900 (4096, 1, [0; 1; 2],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query901 *)
let HOQ_QUERY901 = slq_hist 901 (4096, 1, [0; 2; 3],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query902 *)
let HOQ_QUERY902 = slq_hist 902 (4096, 1, [1; 2; 3],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query903 *)
let HOQ_QUERY903 = slq_hist 903 (4096, 1, [0; 1; 4],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query904 *)
let HOQ_QUERY904 = slq_hist 904 (4096, 1, [0; 2; 4],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query905 *)
let HOQ_QUERY905 = slq_hist 905 (4096, 1, [1; 2; 4],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query906 *)
let HOQ_QUERY906 = slq_hist 906 (4096, 1, [0; 3; 4],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query907 *)
let HOQ_QUERY907 = slq_hist 907 (4096, 1, [1; 3; 4],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query908 *)
let HOQ_QUERY908 = slq_hist 908 (4096, 1, [2; 3; 4],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query909 *)
let HOQ_QUERY909 = slq_hist 909 (4096, 1, [0; 1; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query910 *)
let HOQ_QUERY910 = slq_hist 910 (4096, 1, [0; 2; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query911 *)
let HOQ_QUERY911 = slq_hist 911 (4096, 1, [1; 2; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query912 *)
let HOQ_QUERY912 = slq_hist 912 (4096, 1, [0; 3; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query913 *)
let HOQ_QUERY913 = slq_hist 913 (4096, 1, [1; 3; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query914 *)
let HOQ_QUERY914 = slq_hist 914 (4096, 1, [2; 3; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query915 *)
let HOQ_QUERY915 = slq_hist 915 (4096, 1, [0; 4; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query916 *)
let HOQ_QUERY916 = slq_hist 916 (4096, 1, [1; 4; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query917 *)
let HOQ_QUERY917 = slq_hist 917 (4096, 1, [2; 4; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query918 *)
let HOQ_QUERY918 = slq_hist 918 (4096, 1, [3; 4; 5],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query919 *)
let HOQ_QUERY919 = slq_hist 919 (4096, 1, [0; 1; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query920 *)
let HOQ_QUERY920 = slq_hist 920 (4096, 1, [0; 2; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query921 *)
let HOQ_QUERY921 = slq_hist 921 (4096, 1, [1; 2; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query922 *)
let HOQ_QUERY922 = slq_hist 922 (4096, 1, [0; 3; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query923 *)
let HOQ_QUERY923 = slq_hist 923 (4096, 1, [1; 3; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query924 *)
let HOQ_QUERY924 = slq_hist 924 (4096, 1, [2; 3; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query925 *)
let HOQ_QUERY925 = slq_hist 925 (4096, 1, [0; 4; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query926 *)
let HOQ_QUERY926 = slq_hist 926 (4096, 1, [1; 4; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query927 *)
let HOQ_QUERY927 = slq_hist 927 (4096, 1, [2; 4; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
