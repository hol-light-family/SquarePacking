(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries015.lean                          *)
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

(* Lean: query480 *)
let HOQ_QUERY480 = slq_hist 480 (16, 1, [1; 2; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query481 *)
let HOQ_QUERY481 = slq_hist 481 (16, 1, [3; 6],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query482 *)
let HOQ_QUERY482 = slq_hist 482 (16, 1, [0; 3; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query483 *)
let HOQ_QUERY483 = slq_hist 483 (16, 1, [1; 3; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query484 *)
let HOQ_QUERY484 = slq_hist 484 (16, 1, [2; 3; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query485 *)
let HOQ_QUERY485 = slq_hist 485 (16, 1, [4; 6],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query486 *)
let HOQ_QUERY486 = slq_hist 486 (16, 1, [0; 4; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query487 *)
let HOQ_QUERY487 = slq_hist 487 (16, 1, [1; 4; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query488 *)
let HOQ_QUERY488 = slq_hist 488 (16, 1, [2; 4; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query489 *)
let HOQ_QUERY489 = slq_hist 489 (16, 1, [3; 4; 6],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query490 *)
let HOQ_QUERY490 = slq_hist 490 (16, 1, [5; 6],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query491 *)
let HOQ_QUERY491 = slq_hist 491 (16, 1, [0; 5; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query492 *)
let HOQ_QUERY492 = slq_hist 492 (16, 1, [1; 5; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query493 *)
let HOQ_QUERY493 = slq_hist 493 (16, 1, [2; 5; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query494 *)
let HOQ_QUERY494 = slq_hist 494 (16, 1, [3; 5; 6],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query495 *)
let HOQ_QUERY495 = slq_hist 495 (16, 1, [4; 5; 6],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query496 *)
let HOQ_QUERY496 = slq_hist 496 (16, 1, [0; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query497 *)
let HOQ_QUERY497 = slq_hist 497 (16, 1, [1; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "72/25", nlin_rat "3"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query498 *)
let HOQ_QUERY498 = slq_hist 498 (16, 1, [0; 1; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query499 *)
let HOQ_QUERY499 = slq_hist 499 (16, 1, [2; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query500 *)
let HOQ_QUERY500 = slq_hist 500 (16, 1, [0; 2; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query501 *)
let HOQ_QUERY501 = slq_hist 501 (16, 1, [1; 2; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query502 *)
let HOQ_QUERY502 = slq_hist 502 (16, 1, [3; 7],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query503 *)
let HOQ_QUERY503 = slq_hist 503 (16, 1, [0; 3; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query504 *)
let HOQ_QUERY504 = slq_hist 504 (16, 1, [1; 3; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query505 *)
let HOQ_QUERY505 = slq_hist 505 (16, 1, [2; 3; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query506 *)
let HOQ_QUERY506 = slq_hist 506 (16, 1, [4; 7],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "72/25", nlin_rat "3"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query507 *)
let HOQ_QUERY507 = slq_hist 507 (16, 1, [0; 4; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query508 *)
let HOQ_QUERY508 = slq_hist 508 (16, 1, [1; 4; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "72/25", nlin_rat "3"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query509 *)
let HOQ_QUERY509 = slq_hist 509 (16, 1, [2; 4; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query510 *)
let HOQ_QUERY510 = slq_hist 510 (16, 1, [3; 4; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query511 *)
let HOQ_QUERY511 = slq_hist 511 (16, 1, [5; 7],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
