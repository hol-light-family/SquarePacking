(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries013.lean                          *)
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

(* Lean: query416 *)
let HOQ_QUERY416 = slq_hist 416 (12, 1, [2; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query417 *)
let HOQ_QUERY417 = slq_hist 417 (12, 1, [3; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query418 *)
let HOQ_QUERY418 = slq_hist 418 (12, 1, [4; 7],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query419 *)
let HOQ_QUERY419 = slq_hist 419 (12, 1, [5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query420 *)
let HOQ_QUERY420 = slq_hist 420 (12, 1, [6; 7],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query421 *)
let HOQ_QUERY421 = slq_hist 421 (12, 1, [0; 8],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query422 *)
let HOQ_QUERY422 = slq_hist 422 (12, 1, [1; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query423 *)
let HOQ_QUERY423 = slq_hist 423 (12, 1, [2; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query424 *)
let HOQ_QUERY424 = slq_hist 424 (12, 1, [3; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query425 *)
let HOQ_QUERY425 = slq_hist 425 (12, 1, [4; 8],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query426 *)
let HOQ_QUERY426 = slq_hist 426 (12, 1, [6; 8],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query427 *)
let HOQ_QUERY427 = slq_hist 427 (12, 1, [7; 8],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query428 *)
let HOQ_QUERY428 = slq_hist 428 (12, 1, [9],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5")]);;
(* Lean: query429 *)
let HOQ_QUERY429 = slq_hist 429 (12, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query430 *)
let HOQ_QUERY430 = slq_hist 430 (12, 1, [1; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query431 *)
let HOQ_QUERY431 = slq_hist 431 (12, 1, [2; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query432 *)
let HOQ_QUERY432 = slq_hist 432 (12, 1, [3; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query433 *)
let HOQ_QUERY433 = slq_hist 433 (12, 1, [4; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query434 *)
let HOQ_QUERY434 = slq_hist 434 (12, 1, [5; 9],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5")]);;
(* Lean: query435 *)
let HOQ_QUERY435 = slq_hist 435 (12, 1, [6; 9],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5")]);;
(* Lean: query436 *)
let HOQ_QUERY436 = slq_hist 436 (12, 1, [7; 9],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5")]);;
(* Lean: query437 *)
let HOQ_QUERY437 = slq_hist 437 (12, 1, [8; 9],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query438 *)
let HOQ_QUERY438 = slq_hist 438 (12, 2, [15],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]);;
(* Lean: query439 *)
let HOQ_QUERY439 = slq_hist 439 (12, 2, [15; 18],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]);;
(* Lean: query440 *)
let HOQ_QUERY440 = slq_hist 440 (16, 1, [0; 1],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query441 *)
let HOQ_QUERY441 = slq_hist 441 (16, 1, [0; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query442 *)
let HOQ_QUERY442 = slq_hist 442 (16, 1, [1; 2],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query443 *)
let HOQ_QUERY443 = slq_hist 443 (16, 1, [0; 1; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query444 *)
let HOQ_QUERY444 = slq_hist 444 (16, 1, [0; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query445 *)
let HOQ_QUERY445 = slq_hist 445 (16, 1, [1; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query446 *)
let HOQ_QUERY446 = slq_hist 446 (16, 1, [0; 1; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query447 *)
let HOQ_QUERY447 = slq_hist 447 (16, 1, [2; 3],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
