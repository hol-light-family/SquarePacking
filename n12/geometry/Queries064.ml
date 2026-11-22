(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries064.lean *)
(* (N12Compact.HistoricalOwnership.Queries): exact inherited local queries.  Each Lean *)
(* checked_local_query is registered with slq_hist n (SharedLocalQueries.ml):*)
(* the HOL kernel re-proves the query from its inside / outside points     *)
(* (a .hull query: its three hull points inside, its fourth point outside; *)
(* a .four query: the transformed FourPointDatum A, B inside, P, E outside; *)
(* a .short query: its cluster points inside, the pattern points outside).  *)
(* HOQ_QUERYn : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>  *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query2048 *)
let HOQ_QUERY2048 = slq_hist 2048 (512, 2, [8; 12; 13; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2049 *)
let HOQ_QUERY2049 = slq_hist 2049 (512, 2, [8; 12; 15; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2050 *)
let HOQ_QUERY2050 = slq_hist 2050 (512, 2, [8; 13; 15; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2051 *)
let HOQ_QUERY2051 = slq_hist 2051 (512, 2, [8; 12; 15; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2052 *)
let HOQ_QUERY2052 = slq_hist 2052 (512, 2, [8; 13; 15; 18],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2053 *)
let HOQ_QUERY2053 = slq_hist 2053 (512, 2, [8; 12; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2054 *)
let HOQ_QUERY2054 = slq_hist 2054 (512, 2, [8; 13; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2055 *)
let HOQ_QUERY2055 = slq_hist 2055 (512, 2, [8; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query2056 *)
let HOQ_QUERY2056 = slq_hist 2056 (512, 2, [4; 8; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query2057 *)
let HOQ_QUERY2057 = slq_hist 2057 (512, 2, [5; 8; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2058 *)
let HOQ_QUERY2058 = slq_hist 2058 (512, 2, [5; 8; 12; 13; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2059 *)
let HOQ_QUERY2059 = slq_hist 2059 (512, 2, [5; 8; 12; 15; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2060 *)
let HOQ_QUERY2060 = slq_hist 2060 (512, 2, [5; 8; 13; 15; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2061 *)
let HOQ_QUERY2061 = slq_hist 2061 (512, 2, [5; 8; 12; 15; 18],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2062 *)
let HOQ_QUERY2062 = slq_hist 2062 (512, 2, [5; 8; 13; 15; 18],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2063 *)
let HOQ_QUERY2063 = slq_hist 2063 (512, 2, [5; 8; 12; 16; 18],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2064 *)
let HOQ_QUERY2064 = slq_hist 2064 (512, 2, [5; 8; 13; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2065 *)
let HOQ_QUERY2065 = slq_hist 2065 (512, 2, [5; 8; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query2066 *)
let HOQ_QUERY2066 = slq_hist 2066 (512, 2, [6; 8; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2067 *)
let HOQ_QUERY2067 = slq_hist 2067 (512, 2, [6; 8; 12; 13; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2068 *)
let HOQ_QUERY2068 = slq_hist 2068 (512, 2, [6; 8; 12; 15; 16],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2069 *)
let HOQ_QUERY2069 = slq_hist 2069 (512, 2, [6; 8; 13; 15; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2070 *)
let HOQ_QUERY2070 = slq_hist 2070 (512, 2, [6; 8; 12; 15; 18],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2071 *)
let HOQ_QUERY2071 = slq_hist 2071 (512, 2, [6; 8; 13; 15; 18],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2072 *)
let HOQ_QUERY2072 = slq_hist 2072 (512, 2, [6; 8; 12; 16; 18],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query2073 *)
let HOQ_QUERY2073 = slq_hist 2073 (512, 2, [6; 8; 13; 16; 18],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2074 *)
let HOQ_QUERY2074 = slq_hist 2074 (512, 2, [6; 8; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query2075 *)
let HOQ_QUERY2075 = slq_hist 2075 (512, 2, [4; 9; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2076 *)
let HOQ_QUERY2076 = slq_hist 2076 (512, 2, [4; 9; 12; 15; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query2077 *)
let HOQ_QUERY2077 = slq_hist 2077 (512, 2, [4; 9; 13; 15; 18],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2078 *)
let HOQ_QUERY2078 = slq_hist 2078 (512, 2, [4; 9; 12; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query2079 *)
let HOQ_QUERY2079 = slq_hist 2079 (512, 2, [4; 9; 13; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
