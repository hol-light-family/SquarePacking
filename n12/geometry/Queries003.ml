(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries003.lean                          *)
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

(* Lean: query96 *)
let HOQ_QUERY96 = slq_hist 96 (34816, 0, [0; 7],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query97 *)
let HOQ_QUERY97 = slq_hist 97 (34816, 0, [1; 7],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query98 *)
let HOQ_QUERY98 = slq_hist 98 (34816, 0, [2; 7],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query99 *)
let HOQ_QUERY99 = slq_hist 99 (34816, 0, [4; 7],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query100 *)
let HOQ_QUERY100 = slq_hist 100 (34816, 0, [6; 7],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query101 *)
let HOQ_QUERY101 = slq_hist 101 (34816, 0, [8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query102 *)
let HOQ_QUERY102 = slq_hist 102 (34816, 0, [0; 8],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query103 *)
let HOQ_QUERY103 = slq_hist 103 (34816, 0, [1; 8],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query104 *)
let HOQ_QUERY104 = slq_hist 104 (34816, 0, [2; 8],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query105 *)
let HOQ_QUERY105 = slq_hist 105 (34816, 0, [3; 8],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query106 *)
let HOQ_QUERY106 = slq_hist 106 (34816, 0, [4; 8],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query107 *)
let HOQ_QUERY107 = slq_hist 107 (34816, 0, [5; 8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query108 *)
let HOQ_QUERY108 = slq_hist 108 (34816, 0, [6; 8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query109 *)
let HOQ_QUERY109 = slq_hist 109 (34816, 0, [7; 8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query110 *)
let HOQ_QUERY110 = slq_hist 110 (34816, 0, [9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query111 *)
let HOQ_QUERY111 = slq_hist 111 (34816, 0, [0; 9],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query112 *)
let HOQ_QUERY112 = slq_hist 112 (34816, 0, [1; 9],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query113 *)
let HOQ_QUERY113 = slq_hist 113 (34816, 0, [2; 9],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query114 *)
let HOQ_QUERY114 = slq_hist 114 (34816, 0, [3; 9],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query115 *)
let HOQ_QUERY115 = slq_hist 115 (34816, 0, [4; 9],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query116 *)
let HOQ_QUERY116 = slq_hist 116 (34816, 0, [5; 9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query117 *)
let HOQ_QUERY117 = slq_hist 117 (34816, 0, [6; 9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query118 *)
let HOQ_QUERY118 = slq_hist 118 (34816, 0, [7; 9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query119 *)
let HOQ_QUERY119 = slq_hist 119 (34816, 0, [8; 9],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query120 *)
let HOQ_QUERY120 = slq_hist 120 (34816, 1, [0],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query121 *)
let HOQ_QUERY121 = slq_hist 121 (34816, 1, [2],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query122 *)
let HOQ_QUERY122 = slq_hist 122 (34816, 1, [5],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query123 *)
let HOQ_QUERY123 = slq_hist 123 (34816, 1, [6],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query124 *)
let HOQ_QUERY124 = slq_hist 124 (34816, 1, [7],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query125 *)
let HOQ_QUERY125 = slq_hist 125 (34816, 1, [8],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query126 *)
let HOQ_QUERY126 = slq_hist 126 (34816, 1, [9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query127 *)
let HOQ_QUERY127 = slq_hist 127 (34816, 2, [3; 11],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
