(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries017.lean                          *)
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

(* Lean: query544 *)
let HOQ_QUERY544 = slq_hist 544 (16, 1, [4; 5; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query545 *)
let HOQ_QUERY545 = slq_hist 545 (16, 1, [6; 8],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query546 *)
let HOQ_QUERY546 = slq_hist 546 (16, 1, [0; 6; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query547 *)
let HOQ_QUERY547 = slq_hist 547 (16, 1, [1; 6; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query548 *)
let HOQ_QUERY548 = slq_hist 548 (16, 1, [2; 6; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query549 *)
let HOQ_QUERY549 = slq_hist 549 (16, 1, [3; 6; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query550 *)
let HOQ_QUERY550 = slq_hist 550 (16, 1, [4; 6; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query551 *)
let HOQ_QUERY551 = slq_hist 551 (16, 1, [5; 6; 8],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query552 *)
let HOQ_QUERY552 = slq_hist 552 (16, 1, [7; 8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query553 *)
let HOQ_QUERY553 = slq_hist 553 (16, 1, [0; 7; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query554 *)
let HOQ_QUERY554 = slq_hist 554 (16, 1, [1; 7; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query555 *)
let HOQ_QUERY555 = slq_hist 555 (16, 1, [2; 7; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query556 *)
let HOQ_QUERY556 = slq_hist 556 (16, 1, [3; 7; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query557 *)
let HOQ_QUERY557 = slq_hist 557 (16, 1, [4; 7; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query558 *)
let HOQ_QUERY558 = slq_hist 558 (16, 1, [5; 7; 8],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query559 *)
let HOQ_QUERY559 = slq_hist 559 (16, 1, [6; 7; 8],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query560 *)
let HOQ_QUERY560 = slq_hist 560 (16, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query561 *)
let HOQ_QUERY561 = slq_hist 561 (16, 1, [1; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query562 *)
let HOQ_QUERY562 = slq_hist 562 (16, 1, [0; 1; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query563 *)
let HOQ_QUERY563 = slq_hist 563 (16, 1, [2; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query564 *)
let HOQ_QUERY564 = slq_hist 564 (16, 1, [0; 2; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query565 *)
let HOQ_QUERY565 = slq_hist 565 (16, 1, [1; 2; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query566 *)
let HOQ_QUERY566 = slq_hist 566 (16, 1, [3; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query567 *)
let HOQ_QUERY567 = slq_hist 567 (16, 1, [0; 3; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query568 *)
let HOQ_QUERY568 = slq_hist 568 (16, 1, [1; 3; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query569 *)
let HOQ_QUERY569 = slq_hist 569 (16, 1, [2; 3; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query570 *)
let HOQ_QUERY570 = slq_hist 570 (16, 1, [4; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query571 *)
let HOQ_QUERY571 = slq_hist 571 (16, 1, [0; 4; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query572 *)
let HOQ_QUERY572 = slq_hist 572 (16, 1, [1; 4; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query573 *)
let HOQ_QUERY573 = slq_hist 573 (16, 1, [2; 4; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query574 *)
let HOQ_QUERY574 = slq_hist 574 (16, 1, [3; 4; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query575 *)
let HOQ_QUERY575 = slq_hist 575 (16, 1, [5; 9],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
