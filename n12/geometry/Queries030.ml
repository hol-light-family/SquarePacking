(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries030.lean                          *)
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

(* Lean: query960 *)
let HOQ_QUERY960 = slq_hist 960 (4096, 1, [2; 3; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query961 *)
let HOQ_QUERY961 = slq_hist 961 (4096, 1, [0; 4; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query962 *)
let HOQ_QUERY962 = slq_hist 962 (4096, 1, [1; 4; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query963 *)
let HOQ_QUERY963 = slq_hist 963 (4096, 1, [2; 4; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query964 *)
let HOQ_QUERY964 = slq_hist 964 (4096, 1, [3; 4; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query965 *)
let HOQ_QUERY965 = slq_hist 965 (4096, 1, [0; 5; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query966 *)
let HOQ_QUERY966 = slq_hist 966 (4096, 1, [1; 5; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query967 *)
let HOQ_QUERY967 = slq_hist 967 (4096, 1, [2; 5; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query968 *)
let HOQ_QUERY968 = slq_hist 968 (4096, 1, [3; 5; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query969 *)
let HOQ_QUERY969 = slq_hist 969 (4096, 1, [4; 5; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query970 *)
let HOQ_QUERY970 = slq_hist 970 (4096, 1, [0; 6; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query971 *)
let HOQ_QUERY971 = slq_hist 971 (4096, 1, [1; 6; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query972 *)
let HOQ_QUERY972 = slq_hist 972 (4096, 1, [2; 6; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query973 *)
let HOQ_QUERY973 = slq_hist 973 (4096, 1, [3; 6; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query974 *)
let HOQ_QUERY974 = slq_hist 974 (4096, 1, [4; 6; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query975 *)
let HOQ_QUERY975 = slq_hist 975 (4096, 1, [5; 6; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976 *)
let HOQ_QUERY976 = slq_hist 976 (4096, 1, [0; 7; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query977 *)
let HOQ_QUERY977 = slq_hist 977 (4096, 1, [1; 7; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query978 *)
let HOQ_QUERY978 = slq_hist 978 (4096, 1, [2; 7; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query979 *)
let HOQ_QUERY979 = slq_hist 979 (4096, 1, [3; 7; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query980 *)
let HOQ_QUERY980 = slq_hist 980 (4096, 1, [4; 7; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query981 *)
let HOQ_QUERY981 = slq_hist 981 (4096, 1, [5; 7; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query982 *)
let HOQ_QUERY982 = slq_hist 982 (4096, 1, [6; 7; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query983 *)
let HOQ_QUERY983 = slq_hist 983 (4096, 1, [0; 1; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query984 *)
let HOQ_QUERY984 = slq_hist 984 (4096, 1, [0; 2; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query985 *)
let HOQ_QUERY985 = slq_hist 985 (4096, 1, [1; 2; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query986 *)
let HOQ_QUERY986 = slq_hist 986 (4096, 1, [0; 3; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query987 *)
let HOQ_QUERY987 = slq_hist 987 (4096, 1, [1; 3; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query988 *)
let HOQ_QUERY988 = slq_hist 988 (4096, 1, [2; 3; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query989 *)
let HOQ_QUERY989 = slq_hist 989 (4096, 1, [0; 4; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query990 *)
let HOQ_QUERY990 = slq_hist 990 (4096, 1, [1; 4; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query991 *)
let HOQ_QUERY991 = slq_hist 991 (4096, 1, [2; 4; 9],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
