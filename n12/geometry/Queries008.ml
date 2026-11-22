(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries008.lean                          *)
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

(* Lean: query256 *)
let HOQ_QUERY256 = slq_hist 256 (1, 1, [5; 7; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query257 *)
let HOQ_QUERY257 = slq_hist 257 (1, 1, [6; 7; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query258 *)
let HOQ_QUERY258 = slq_hist 258 (1, 1, [0; 8; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query259 *)
let HOQ_QUERY259 = slq_hist 259 (1, 1, [1; 8; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query260 *)
let HOQ_QUERY260 = slq_hist 260 (1, 1, [2; 8; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500")]);;
(* Lean: query261 *)
let HOQ_QUERY261 = slq_hist 261 (1, 1, [3; 8; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query262 *)
let HOQ_QUERY262 = slq_hist 262 (1, 1, [4; 8; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query263 *)
let HOQ_QUERY263 = slq_hist 263 (1, 1, [5; 8; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query264 *)
let HOQ_QUERY264 = slq_hist 264 (1, 1, [6; 8; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query265 *)
let HOQ_QUERY265 = slq_hist 265 (1, 1, [7; 8; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query266 *)
let HOQ_QUERY266 = slq_hist 266 (2, 1, [0; 1; 2],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query267 *)
let HOQ_QUERY267 = slq_hist 267 (2, 1, [0; 1; 3],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query268 *)
let HOQ_QUERY268 = slq_hist 268 (2, 1, [0; 2; 3],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query269 *)
let HOQ_QUERY269 = slq_hist 269 (2, 1, [1; 2; 3],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query270 *)
let HOQ_QUERY270 = slq_hist 270 (2, 1, [0; 1; 4],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query271 *)
let HOQ_QUERY271 = slq_hist 271 (2, 1, [0; 2; 4],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query272 *)
let HOQ_QUERY272 = slq_hist 272 (2, 1, [1; 2; 4],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query273 *)
let HOQ_QUERY273 = slq_hist 273 (2, 1, [0; 3; 4],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query274 *)
let HOQ_QUERY274 = slq_hist 274 (2, 1, [1; 3; 4],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query275 *)
let HOQ_QUERY275 = slq_hist 275 (2, 1, [2; 3; 4],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query276 *)
let HOQ_QUERY276 = slq_hist 276 (2, 1, [0; 1; 5],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query277 *)
let HOQ_QUERY277 = slq_hist 277 (2, 1, [0; 2; 5],
  [(nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query278 *)
let HOQ_QUERY278 = slq_hist 278 (2, 1, [1; 2; 5],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query279 *)
let HOQ_QUERY279 = slq_hist 279 (2, 1, [0; 3; 5],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query280 *)
let HOQ_QUERY280 = slq_hist 280 (2, 1, [1; 3; 5],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query281 *)
let HOQ_QUERY281 = slq_hist 281 (2, 1, [2; 3; 5],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query282 *)
let HOQ_QUERY282 = slq_hist 282 (2, 1, [0; 4; 5],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query283 *)
let HOQ_QUERY283 = slq_hist 283 (2, 1, [1; 4; 5],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query284 *)
let HOQ_QUERY284 = slq_hist 284 (2, 1, [2; 4; 5],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query285 *)
let HOQ_QUERY285 = slq_hist 285 (2, 1, [3; 4; 5],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query286 *)
let HOQ_QUERY286 = slq_hist 286 (2, 1, [0; 1; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query287 *)
let HOQ_QUERY287 = slq_hist 287 (2, 1, [0; 2; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
