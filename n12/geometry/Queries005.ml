(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries005.lean                          *)
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

(* Lean: query160 *)
let HOQ_QUERY160 = slq_hist 160 (1, 1, [1; 3; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query161 *)
let HOQ_QUERY161 = slq_hist 161 (1, 1, [2; 3; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query162 *)
let HOQ_QUERY162 = slq_hist 162 (1, 1, [0; 4; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query163 *)
let HOQ_QUERY163 = slq_hist 163 (1, 1, [1; 4; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query164 *)
let HOQ_QUERY164 = slq_hist 164 (1, 1, [2; 4; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query165 *)
let HOQ_QUERY165 = slq_hist 165 (1, 1, [3; 4; 5],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query166 *)
let HOQ_QUERY166 = slq_hist 166 (1, 1, [0; 1; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query167 *)
let HOQ_QUERY167 = slq_hist 167 (1, 1, [0; 2; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query168 *)
let HOQ_QUERY168 = slq_hist 168 (1, 1, [1; 2; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query169 *)
let HOQ_QUERY169 = slq_hist 169 (1, 1, [0; 3; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query170 *)
let HOQ_QUERY170 = slq_hist 170 (1, 1, [1; 3; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query171 *)
let HOQ_QUERY171 = slq_hist 171 (1, 1, [2; 3; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query172 *)
let HOQ_QUERY172 = slq_hist 172 (1, 1, [0; 4; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query173 *)
let HOQ_QUERY173 = slq_hist 173 (1, 1, [1; 4; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query174 *)
let HOQ_QUERY174 = slq_hist 174 (1, 1, [2; 4; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query175 *)
let HOQ_QUERY175 = slq_hist 175 (1, 1, [3; 4; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query176 *)
let HOQ_QUERY176 = slq_hist 176 (1, 1, [0; 5; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query177 *)
let HOQ_QUERY177 = slq_hist 177 (1, 1, [1; 5; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query178 *)
let HOQ_QUERY178 = slq_hist 178 (1, 1, [2; 5; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500")]);;
(* Lean: query179 *)
let HOQ_QUERY179 = slq_hist 179 (1, 1, [3; 5; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query180 *)
let HOQ_QUERY180 = slq_hist 180 (1, 1, [4; 5; 6],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query181 *)
let HOQ_QUERY181 = slq_hist 181 (1, 1, [0; 1; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query182 *)
let HOQ_QUERY182 = slq_hist 182 (1, 1, [0; 2; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query183 *)
let HOQ_QUERY183 = slq_hist 183 (1, 1, [1; 2; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query184 *)
let HOQ_QUERY184 = slq_hist 184 (1, 1, [0; 3; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query185 *)
let HOQ_QUERY185 = slq_hist 185 (1, 1, [1; 3; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query186 *)
let HOQ_QUERY186 = slq_hist 186 (1, 1, [2; 3; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query187 *)
let HOQ_QUERY187 = slq_hist 187 (1, 1, [0; 4; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query188 *)
let HOQ_QUERY188 = slq_hist 188 (1, 1, [1; 4; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query189 *)
let HOQ_QUERY189 = slq_hist 189 (1, 1, [2; 4; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query190 *)
let HOQ_QUERY190 = slq_hist 190 (1, 1, [3; 4; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query191 *)
let HOQ_QUERY191 = slq_hist 191 (1, 1, [0; 5; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
