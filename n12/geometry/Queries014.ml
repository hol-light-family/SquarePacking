(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries014.lean                          *)
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

(* Lean: query448 *)
let HOQ_QUERY448 = slq_hist 448 (16, 1, [0; 2; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query449 *)
let HOQ_QUERY449 = slq_hist 449 (16, 1, [1; 2; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query450 *)
let HOQ_QUERY450 = slq_hist 450 (16, 1, [0; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query451 *)
let HOQ_QUERY451 = slq_hist 451 (16, 1, [1; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "72/25", nlin_rat "3"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query452 *)
let HOQ_QUERY452 = slq_hist 452 (16, 1, [0; 1; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query453 *)
let HOQ_QUERY453 = slq_hist 453 (16, 1, [2; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query454 *)
let HOQ_QUERY454 = slq_hist 454 (16, 1, [0; 2; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query455 *)
let HOQ_QUERY455 = slq_hist 455 (16, 1, [1; 2; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query456 *)
let HOQ_QUERY456 = slq_hist 456 (16, 1, [3; 4],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query457 *)
let HOQ_QUERY457 = slq_hist 457 (16, 1, [0; 3; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query458 *)
let HOQ_QUERY458 = slq_hist 458 (16, 1, [1; 3; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query459 *)
let HOQ_QUERY459 = slq_hist 459 (16, 1, [2; 3; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query460 *)
let HOQ_QUERY460 = slq_hist 460 (16, 1, [0; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query461 *)
let HOQ_QUERY461 = slq_hist 461 (16, 1, [1; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query462 *)
let HOQ_QUERY462 = slq_hist 462 (16, 1, [0; 1; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query463 *)
let HOQ_QUERY463 = slq_hist 463 (16, 1, [2; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query464 *)
let HOQ_QUERY464 = slq_hist 464 (16, 1, [0; 2; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query465 *)
let HOQ_QUERY465 = slq_hist 465 (16, 1, [1; 2; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query466 *)
let HOQ_QUERY466 = slq_hist 466 (16, 1, [3; 5],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query467 *)
let HOQ_QUERY467 = slq_hist 467 (16, 1, [0; 3; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query468 *)
let HOQ_QUERY468 = slq_hist 468 (16, 1, [1; 3; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query469 *)
let HOQ_QUERY469 = slq_hist 469 (16, 1, [2; 3; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query470 *)
let HOQ_QUERY470 = slq_hist 470 (16, 1, [4; 5],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query471 *)
let HOQ_QUERY471 = slq_hist 471 (16, 1, [0; 4; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query472 *)
let HOQ_QUERY472 = slq_hist 472 (16, 1, [1; 4; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query473 *)
let HOQ_QUERY473 = slq_hist 473 (16, 1, [2; 4; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query474 *)
let HOQ_QUERY474 = slq_hist 474 (16, 1, [3; 4; 5],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query475 *)
let HOQ_QUERY475 = slq_hist 475 (16, 1, [0; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query476 *)
let HOQ_QUERY476 = slq_hist 476 (16, 1, [1; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query477 *)
let HOQ_QUERY477 = slq_hist 477 (16, 1, [0; 1; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query478 *)
let HOQ_QUERY478 = slq_hist 478 (16, 1, [2; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query479 *)
let HOQ_QUERY479 = slq_hist 479 (16, 1, [0; 2; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
