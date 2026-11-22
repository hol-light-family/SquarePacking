(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries006.lean                          *)
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

(* Lean: query192 *)
let HOQ_QUERY192 = slq_hist 192 (1, 1, [1; 5; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query193 *)
let HOQ_QUERY193 = slq_hist 193 (1, 1, [2; 5; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query194 *)
let HOQ_QUERY194 = slq_hist 194 (1, 1, [3; 5; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query195 *)
let HOQ_QUERY195 = slq_hist 195 (1, 1, [4; 5; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query196 *)
let HOQ_QUERY196 = slq_hist 196 (1, 1, [0; 6; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query197 *)
let HOQ_QUERY197 = slq_hist 197 (1, 1, [1; 6; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query198 *)
let HOQ_QUERY198 = slq_hist 198 (1, 1, [2; 6; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query199 *)
let HOQ_QUERY199 = slq_hist 199 (1, 1, [3; 6; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query200 *)
let HOQ_QUERY200 = slq_hist 200 (1, 1, [4; 6; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query201 *)
let HOQ_QUERY201 = slq_hist 201 (1, 1, [5; 6; 7],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query202 *)
let HOQ_QUERY202 = slq_hist 202 (1, 1, [0; 1; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query203 *)
let HOQ_QUERY203 = slq_hist 203 (1, 1, [0; 2; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500")]);;
(* Lean: query204 *)
let HOQ_QUERY204 = slq_hist 204 (1, 1, [1; 2; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query205 *)
let HOQ_QUERY205 = slq_hist 205 (1, 1, [0; 3; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query206 *)
let HOQ_QUERY206 = slq_hist 206 (1, 1, [1; 3; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query207 *)
let HOQ_QUERY207 = slq_hist 207 (1, 1, [2; 3; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query208 *)
let HOQ_QUERY208 = slq_hist 208 (1, 1, [0; 4; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query209 *)
let HOQ_QUERY209 = slq_hist 209 (1, 1, [1; 4; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query210 *)
let HOQ_QUERY210 = slq_hist 210 (1, 1, [2; 4; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query211 *)
let HOQ_QUERY211 = slq_hist 211 (1, 1, [3; 4; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query212 *)
let HOQ_QUERY212 = slq_hist 212 (1, 1, [0; 5; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query213 *)
let HOQ_QUERY213 = slq_hist 213 (1, 1, [1; 5; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query214 *)
let HOQ_QUERY214 = slq_hist 214 (1, 1, [2; 5; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500")]);;
(* Lean: query215 *)
let HOQ_QUERY215 = slq_hist 215 (1, 1, [3; 5; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query216 *)
let HOQ_QUERY216 = slq_hist 216 (1, 1, [4; 5; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query217 *)
let HOQ_QUERY217 = slq_hist 217 (1, 1, [0; 6; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query218 *)
let HOQ_QUERY218 = slq_hist 218 (1, 1, [1; 6; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query219 *)
let HOQ_QUERY219 = slq_hist 219 (1, 1, [2; 6; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500")]);;
(* Lean: query220 *)
let HOQ_QUERY220 = slq_hist 220 (1, 1, [3; 6; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query221 *)
let HOQ_QUERY221 = slq_hist 221 (1, 1, [4; 6; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query222 *)
let HOQ_QUERY222 = slq_hist 222 (1, 1, [5; 6; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query223 *)
let HOQ_QUERY223 = slq_hist 223 (1, 1, [0; 7; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
