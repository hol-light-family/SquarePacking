(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries016.lean                          *)
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

(* Lean: query512 *)
let HOQ_QUERY512 = slq_hist 512 (16, 1, [0; 5; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query513 *)
let HOQ_QUERY513 = slq_hist 513 (16, 1, [1; 5; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query514 *)
let HOQ_QUERY514 = slq_hist 514 (16, 1, [2; 5; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query515 *)
let HOQ_QUERY515 = slq_hist 515 (16, 1, [3; 5; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query516 *)
let HOQ_QUERY516 = slq_hist 516 (16, 1, [4; 5; 7],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query517 *)
let HOQ_QUERY517 = slq_hist 517 (16, 1, [6; 7],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query518 *)
let HOQ_QUERY518 = slq_hist 518 (16, 1, [0; 6; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query519 *)
let HOQ_QUERY519 = slq_hist 519 (16, 1, [1; 6; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query520 *)
let HOQ_QUERY520 = slq_hist 520 (16, 1, [2; 6; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query521 *)
let HOQ_QUERY521 = slq_hist 521 (16, 1, [3; 6; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query522 *)
let HOQ_QUERY522 = slq_hist 522 (16, 1, [4; 6; 7],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query523 *)
let HOQ_QUERY523 = slq_hist 523 (16, 1, [5; 6; 7],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query524 *)
let HOQ_QUERY524 = slq_hist 524 (16, 1, [0; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query525 *)
let HOQ_QUERY525 = slq_hist 525 (16, 1, [1; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query526 *)
let HOQ_QUERY526 = slq_hist 526 (16, 1, [0; 1; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query527 *)
let HOQ_QUERY527 = slq_hist 527 (16, 1, [2; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query528 *)
let HOQ_QUERY528 = slq_hist 528 (16, 1, [0; 2; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query529 *)
let HOQ_QUERY529 = slq_hist 529 (16, 1, [1; 2; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query530 *)
let HOQ_QUERY530 = slq_hist 530 (16, 1, [3; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query531 *)
let HOQ_QUERY531 = slq_hist 531 (16, 1, [0; 3; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query532 *)
let HOQ_QUERY532 = slq_hist 532 (16, 1, [1; 3; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query533 *)
let HOQ_QUERY533 = slq_hist 533 (16, 1, [2; 3; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query534 *)
let HOQ_QUERY534 = slq_hist 534 (16, 1, [4; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query535 *)
let HOQ_QUERY535 = slq_hist 535 (16, 1, [0; 4; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query536 *)
let HOQ_QUERY536 = slq_hist 536 (16, 1, [1; 4; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query537 *)
let HOQ_QUERY537 = slq_hist 537 (16, 1, [2; 4; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query538 *)
let HOQ_QUERY538 = slq_hist 538 (16, 1, [3; 4; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query539 *)
let HOQ_QUERY539 = slq_hist 539 (16, 1, [5; 8],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query540 *)
let HOQ_QUERY540 = slq_hist 540 (16, 1, [0; 5; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query541 *)
let HOQ_QUERY541 = slq_hist 541 (16, 1, [1; 5; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query542 *)
let HOQ_QUERY542 = slq_hist 542 (16, 1, [2; 5; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query543 *)
let HOQ_QUERY543 = slq_hist 543 (16, 1, [3; 5; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
