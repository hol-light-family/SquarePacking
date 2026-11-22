(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries010.lean                          *)
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

(* Lean: query320 *)
let HOQ_QUERY320 = slq_hist 320 (2, 1, [4; 6; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query321 *)
let HOQ_QUERY321 = slq_hist 321 (2, 1, [5; 6; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query322 *)
let HOQ_QUERY322 = slq_hist 322 (2, 1, [0; 1; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query323 *)
let HOQ_QUERY323 = slq_hist 323 (2, 1, [0; 2; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query324 *)
let HOQ_QUERY324 = slq_hist 324 (2, 1, [1; 2; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query325 *)
let HOQ_QUERY325 = slq_hist 325 (2, 1, [0; 3; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query326 *)
let HOQ_QUERY326 = slq_hist 326 (2, 1, [1; 3; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query327 *)
let HOQ_QUERY327 = slq_hist 327 (2, 1, [2; 3; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query328 *)
let HOQ_QUERY328 = slq_hist 328 (2, 1, [0; 4; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query329 *)
let HOQ_QUERY329 = slq_hist 329 (2, 1, [1; 4; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query330 *)
let HOQ_QUERY330 = slq_hist 330 (2, 1, [2; 4; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query331 *)
let HOQ_QUERY331 = slq_hist 331 (2, 1, [3; 4; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query332 *)
let HOQ_QUERY332 = slq_hist 332 (2, 1, [0; 5; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query333 *)
let HOQ_QUERY333 = slq_hist 333 (2, 1, [1; 5; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query334 *)
let HOQ_QUERY334 = slq_hist 334 (2, 1, [2; 5; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query335 *)
let HOQ_QUERY335 = slq_hist 335 (2, 1, [3; 5; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query336 *)
let HOQ_QUERY336 = slq_hist 336 (2, 1, [4; 5; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query337 *)
let HOQ_QUERY337 = slq_hist 337 (2, 1, [0; 6; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query338 *)
let HOQ_QUERY338 = slq_hist 338 (2, 1, [1; 6; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query339 *)
let HOQ_QUERY339 = slq_hist 339 (2, 1, [2; 6; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query340 *)
let HOQ_QUERY340 = slq_hist 340 (2, 1, [3; 6; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query341 *)
let HOQ_QUERY341 = slq_hist 341 (2, 1, [4; 6; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query342 *)
let HOQ_QUERY342 = slq_hist 342 (2, 1, [5; 6; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query343 *)
let HOQ_QUERY343 = slq_hist 343 (2, 1, [0; 7; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query344 *)
let HOQ_QUERY344 = slq_hist 344 (2, 1, [1; 7; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query345 *)
let HOQ_QUERY345 = slq_hist 345 (2, 1, [2; 7; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query346 *)
let HOQ_QUERY346 = slq_hist 346 (2, 1, [3; 7; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query347 *)
let HOQ_QUERY347 = slq_hist 347 (2, 1, [4; 7; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query348 *)
let HOQ_QUERY348 = slq_hist 348 (2, 1, [5; 7; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query349 *)
let HOQ_QUERY349 = slq_hist 349 (2, 1, [6; 7; 8],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query350 *)
let HOQ_QUERY350 = slq_hist 350 (2, 1, [0; 1; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query351 *)
let HOQ_QUERY351 = slq_hist 351 (2, 1, [0; 2; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
