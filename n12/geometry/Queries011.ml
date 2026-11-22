(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries011.lean                          *)
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

(* Lean: query352 *)
let HOQ_QUERY352 = slq_hist 352 (2, 1, [1; 2; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query353 *)
let HOQ_QUERY353 = slq_hist 353 (2, 1, [0; 3; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query354 *)
let HOQ_QUERY354 = slq_hist 354 (2, 1, [1; 3; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query355 *)
let HOQ_QUERY355 = slq_hist 355 (2, 1, [2; 3; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query356 *)
let HOQ_QUERY356 = slq_hist 356 (2, 1, [0; 4; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query357 *)
let HOQ_QUERY357 = slq_hist 357 (2, 1, [1; 4; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query358 *)
let HOQ_QUERY358 = slq_hist 358 (2, 1, [2; 4; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query359 *)
let HOQ_QUERY359 = slq_hist 359 (2, 1, [3; 4; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query360 *)
let HOQ_QUERY360 = slq_hist 360 (2, 1, [0; 5; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query361 *)
let HOQ_QUERY361 = slq_hist 361 (2, 1, [1; 5; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query362 *)
let HOQ_QUERY362 = slq_hist 362 (2, 1, [2; 5; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query363 *)
let HOQ_QUERY363 = slq_hist 363 (2, 1, [3; 5; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query364 *)
let HOQ_QUERY364 = slq_hist 364 (2, 1, [4; 5; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query365 *)
let HOQ_QUERY365 = slq_hist 365 (2, 1, [0; 6; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query366 *)
let HOQ_QUERY366 = slq_hist 366 (2, 1, [1; 6; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query367 *)
let HOQ_QUERY367 = slq_hist 367 (2, 1, [2; 6; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query368 *)
let HOQ_QUERY368 = slq_hist 368 (2, 1, [3; 6; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query369 *)
let HOQ_QUERY369 = slq_hist 369 (2, 1, [4; 6; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query370 *)
let HOQ_QUERY370 = slq_hist 370 (2, 1, [5; 6; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query371 *)
let HOQ_QUERY371 = slq_hist 371 (2, 1, [0; 7; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query372 *)
let HOQ_QUERY372 = slq_hist 372 (2, 1, [1; 7; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query373 *)
let HOQ_QUERY373 = slq_hist 373 (2, 1, [2; 7; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query374 *)
let HOQ_QUERY374 = slq_hist 374 (2, 1, [3; 7; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query375 *)
let HOQ_QUERY375 = slq_hist 375 (2, 1, [4; 7; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query376 *)
let HOQ_QUERY376 = slq_hist 376 (2, 1, [5; 7; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query377 *)
let HOQ_QUERY377 = slq_hist 377 (2, 1, [6; 7; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query378 *)
let HOQ_QUERY378 = slq_hist 378 (2, 1, [0; 8; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query379 *)
let HOQ_QUERY379 = slq_hist 379 (2, 1, [1; 8; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query380 *)
let HOQ_QUERY380 = slq_hist 380 (2, 1, [2; 8; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query381 *)
let HOQ_QUERY381 = slq_hist 381 (2, 1, [3; 8; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query382 *)
let HOQ_QUERY382 = slq_hist 382 (2, 1, [4; 8; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query383 *)
let HOQ_QUERY383 = slq_hist 383 (2, 1, [5; 8; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
