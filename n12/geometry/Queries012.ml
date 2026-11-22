(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries012.lean                          *)
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

(* Lean: query384 *)
let HOQ_QUERY384 = slq_hist 384 (2, 1, [6; 8; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query385 *)
let HOQ_QUERY385 = slq_hist 385 (2, 1, [7; 8; 9],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query386 *)
let HOQ_QUERY386 = slq_hist 386 (12, 1, [0],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query387 *)
let HOQ_QUERY387 = slq_hist 387 (12, 1, [1],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query388 *)
let HOQ_QUERY388 = slq_hist 388 (12, 1, [0; 1],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query389 *)
let HOQ_QUERY389 = slq_hist 389 (12, 1, [2],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query390 *)
let HOQ_QUERY390 = slq_hist 390 (12, 1, [0; 2],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query391 *)
let HOQ_QUERY391 = slq_hist 391 (12, 1, [1; 2],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "457/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query392 *)
let HOQ_QUERY392 = slq_hist 392 (12, 1, [3],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query393 *)
let HOQ_QUERY393 = slq_hist 393 (12, 1, [0; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query394 *)
let HOQ_QUERY394 = slq_hist 394 (12, 1, [1; 3],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query395 *)
let HOQ_QUERY395 = slq_hist 395 (12, 1, [2; 3],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query396 *)
let HOQ_QUERY396 = slq_hist 396 (12, 1, [4],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query397 *)
let HOQ_QUERY397 = slq_hist 397 (12, 1, [0; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query398 *)
let HOQ_QUERY398 = slq_hist 398 (12, 1, [1; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query399 *)
let HOQ_QUERY399 = slq_hist 399 (12, 1, [2; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query400 *)
let HOQ_QUERY400 = slq_hist 400 (12, 1, [3; 4],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query401 *)
let HOQ_QUERY401 = slq_hist 401 (12, 1, [0; 5],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query402 *)
let HOQ_QUERY402 = slq_hist 402 (12, 1, [1; 5],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query403 *)
let HOQ_QUERY403 = slq_hist 403 (12, 1, [2; 5],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query404 *)
let HOQ_QUERY404 = slq_hist 404 (12, 1, [3; 5],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query405 *)
let HOQ_QUERY405 = slq_hist 405 (12, 1, [4; 5],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "457/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query406 *)
let HOQ_QUERY406 = slq_hist 406 (12, 1, [6],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query407 *)
let HOQ_QUERY407 = slq_hist 407 (12, 1, [0; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query408 *)
let HOQ_QUERY408 = slq_hist 408 (12, 1, [1; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query409 *)
let HOQ_QUERY409 = slq_hist 409 (12, 1, [2; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query410 *)
let HOQ_QUERY410 = slq_hist 410 (12, 1, [3; 6],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query411 *)
let HOQ_QUERY411 = slq_hist 411 (12, 1, [4; 6],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query412 *)
let HOQ_QUERY412 = slq_hist 412 (12, 1, [5; 6],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query413 *)
let HOQ_QUERY413 = slq_hist 413 (12, 1, [7],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query414 *)
let HOQ_QUERY414 = slq_hist 414 (12, 1, [0; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query415 *)
let HOQ_QUERY415 = slq_hist 415 (12, 1, [1; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
