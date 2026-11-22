(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries029.lean                          *)
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

(* Lean: query928 *)
let HOQ_QUERY928 = slq_hist 928 (4096, 1, [3; 4; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query929 *)
let HOQ_QUERY929 = slq_hist 929 (4096, 1, [0; 5; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query930 *)
let HOQ_QUERY930 = slq_hist 930 (4096, 1, [1; 5; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query931 *)
let HOQ_QUERY931 = slq_hist 931 (4096, 1, [2; 5; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query932 *)
let HOQ_QUERY932 = slq_hist 932 (4096, 1, [3; 5; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query933 *)
let HOQ_QUERY933 = slq_hist 933 (4096, 1, [4; 5; 6],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query934 *)
let HOQ_QUERY934 = slq_hist 934 (4096, 1, [0; 1; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query935 *)
let HOQ_QUERY935 = slq_hist 935 (4096, 1, [0; 2; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query936 *)
let HOQ_QUERY936 = slq_hist 936 (4096, 1, [1; 2; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query937 *)
let HOQ_QUERY937 = slq_hist 937 (4096, 1, [0; 3; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query938 *)
let HOQ_QUERY938 = slq_hist 938 (4096, 1, [1; 3; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query939 *)
let HOQ_QUERY939 = slq_hist 939 (4096, 1, [2; 3; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query940 *)
let HOQ_QUERY940 = slq_hist 940 (4096, 1, [0; 4; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query941 *)
let HOQ_QUERY941 = slq_hist 941 (4096, 1, [1; 4; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query942 *)
let HOQ_QUERY942 = slq_hist 942 (4096, 1, [2; 4; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query943 *)
let HOQ_QUERY943 = slq_hist 943 (4096, 1, [3; 4; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query944 *)
let HOQ_QUERY944 = slq_hist 944 (4096, 1, [0; 5; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query945 *)
let HOQ_QUERY945 = slq_hist 945 (4096, 1, [1; 5; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query946 *)
let HOQ_QUERY946 = slq_hist 946 (4096, 1, [2; 5; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query947 *)
let HOQ_QUERY947 = slq_hist 947 (4096, 1, [3; 5; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query948 *)
let HOQ_QUERY948 = slq_hist 948 (4096, 1, [4; 5; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query949 *)
let HOQ_QUERY949 = slq_hist 949 (4096, 1, [0; 6; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query950 *)
let HOQ_QUERY950 = slq_hist 950 (4096, 1, [1; 6; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query951 *)
let HOQ_QUERY951 = slq_hist 951 (4096, 1, [2; 6; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query952 *)
let HOQ_QUERY952 = slq_hist 952 (4096, 1, [3; 6; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query953 *)
let HOQ_QUERY953 = slq_hist 953 (4096, 1, [4; 6; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query954 *)
let HOQ_QUERY954 = slq_hist 954 (4096, 1, [5; 6; 7],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query955 *)
let HOQ_QUERY955 = slq_hist 955 (4096, 1, [0; 1; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query956 *)
let HOQ_QUERY956 = slq_hist 956 (4096, 1, [0; 2; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query957 *)
let HOQ_QUERY957 = slq_hist 957 (4096, 1, [1; 2; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query958 *)
let HOQ_QUERY958 = slq_hist 958 (4096, 1, [0; 3; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query959 *)
let HOQ_QUERY959 = slq_hist 959 (4096, 1, [1; 3; 8],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
