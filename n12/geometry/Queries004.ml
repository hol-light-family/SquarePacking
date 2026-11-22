(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries004.lean                          *)
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

(* Lean: query128 *)
let HOQ_QUERY128 = slq_hist 128 (34816, 2, [3; 13],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query129 *)
let HOQ_QUERY129 = slq_hist 129 (34816, 2, [1; 3; 11],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query130 *)
let HOQ_QUERY130 = slq_hist 130 (34816, 2, [1; 3; 13],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query131 *)
let HOQ_QUERY131 = slq_hist 131 (34816, 2, [0; 5; 11],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query132 *)
let HOQ_QUERY132 = slq_hist 132 (34816, 2, [0; 5; 14],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query133 *)
let HOQ_QUERY133 = slq_hist 133 (34816, 2, [3; 5; 11],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query134 *)
let HOQ_QUERY134 = slq_hist 134 (34816, 2, [3; 5; 13],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query135 *)
let HOQ_QUERY135 = slq_hist 135 (34816, 2, [4; 5; 11],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query136 *)
let HOQ_QUERY136 = slq_hist 136 (34816, 2, [4; 5; 14],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query137 *)
let HOQ_QUERY137 = slq_hist 137 (34816, 2, [7; 11],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query138 *)
let HOQ_QUERY138 = slq_hist 138 (34816, 2, [7; 13],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query139 *)
let HOQ_QUERY139 = slq_hist 139 (34816, 2, [7; 14],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query140 *)
let HOQ_QUERY140 = slq_hist 140 (34816, 2, [3; 7; 11],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query141 *)
let HOQ_QUERY141 = slq_hist 141 (34816, 2, [3; 7; 13],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query142 *)
let HOQ_QUERY142 = slq_hist 142 (34816, 2, [3; 7; 14],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query143 *)
let HOQ_QUERY143 = slq_hist 143 (34816, 2, [5; 7; 11],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query144 *)
let HOQ_QUERY144 = slq_hist 144 (34816, 2, [5; 7; 13],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query145 *)
let HOQ_QUERY145 = slq_hist 145 (34816, 2, [5; 7; 14],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query146 *)
let HOQ_QUERY146 = slq_hist 146 (1, 1, [0; 1; 2],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query147 *)
let HOQ_QUERY147 = slq_hist 147 (1, 1, [0; 1; 3],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query148 *)
let HOQ_QUERY148 = slq_hist 148 (1, 1, [0; 2; 3],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query149 *)
let HOQ_QUERY149 = slq_hist 149 (1, 1, [1; 2; 3],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query150 *)
let HOQ_QUERY150 = slq_hist 150 (1, 1, [0; 1; 4],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query151 *)
let HOQ_QUERY151 = slq_hist 151 (1, 1, [0; 2; 4],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query152 *)
let HOQ_QUERY152 = slq_hist 152 (1, 1, [1; 2; 4],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query153 *)
let HOQ_QUERY153 = slq_hist 153 (1, 1, [0; 3; 4],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query154 *)
let HOQ_QUERY154 = slq_hist 154 (1, 1, [1; 3; 4],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query155 *)
let HOQ_QUERY155 = slq_hist 155 (1, 1, [2; 3; 4],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query156 *)
let HOQ_QUERY156 = slq_hist 156 (1, 1, [0; 1; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query157 *)
let HOQ_QUERY157 = slq_hist 157 (1, 1, [0; 2; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500")]);;
(* Lean: query158 *)
let HOQ_QUERY158 = slq_hist 158 (1, 1, [1; 2; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query159 *)
let HOQ_QUERY159 = slq_hist 159 (1, 1, [0; 3; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
