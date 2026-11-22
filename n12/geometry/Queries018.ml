(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries018.lean                          *)
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

(* Lean: query576 *)
let HOQ_QUERY576 = slq_hist 576 (16, 1, [0; 5; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query577 *)
let HOQ_QUERY577 = slq_hist 577 (16, 1, [1; 5; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query578 *)
let HOQ_QUERY578 = slq_hist 578 (16, 1, [2; 5; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query579 *)
let HOQ_QUERY579 = slq_hist 579 (16, 1, [3; 5; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query580 *)
let HOQ_QUERY580 = slq_hist 580 (16, 1, [4; 5; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query581 *)
let HOQ_QUERY581 = slq_hist 581 (16, 1, [6; 9],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query582 *)
let HOQ_QUERY582 = slq_hist 582 (16, 1, [0; 6; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query583 *)
let HOQ_QUERY583 = slq_hist 583 (16, 1, [1; 6; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query584 *)
let HOQ_QUERY584 = slq_hist 584 (16, 1, [2; 6; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query585 *)
let HOQ_QUERY585 = slq_hist 585 (16, 1, [3; 6; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query586 *)
let HOQ_QUERY586 = slq_hist 586 (16, 1, [4; 6; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query587 *)
let HOQ_QUERY587 = slq_hist 587 (16, 1, [5; 6; 9],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query588 *)
let HOQ_QUERY588 = slq_hist 588 (16, 1, [0; 7; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query589 *)
let HOQ_QUERY589 = slq_hist 589 (16, 1, [1; 7; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query590 *)
let HOQ_QUERY590 = slq_hist 590 (16, 1, [2; 7; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query591 *)
let HOQ_QUERY591 = slq_hist 591 (16, 1, [3; 7; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query592 *)
let HOQ_QUERY592 = slq_hist 592 (16, 1, [4; 7; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query593 *)
let HOQ_QUERY593 = slq_hist 593 (16, 1, [5; 7; 9],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query594 *)
let HOQ_QUERY594 = slq_hist 594 (16, 1, [6; 7; 9],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query595 *)
let HOQ_QUERY595 = slq_hist 595 (16, 1, [8; 9],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query596 *)
let HOQ_QUERY596 = slq_hist 596 (16, 1, [0; 8; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query597 *)
let HOQ_QUERY597 = slq_hist 597 (16, 1, [1; 8; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query598 *)
let HOQ_QUERY598 = slq_hist 598 (16, 1, [2; 8; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query599 *)
let HOQ_QUERY599 = slq_hist 599 (16, 1, [3; 8; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query600 *)
let HOQ_QUERY600 = slq_hist 600 (16, 1, [4; 8; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "213/100", nlin_rat "81/25")],
  [(nlin_rat "2", nlin_rat "1543/500")]);;
(* Lean: query601 *)
let HOQ_QUERY601 = slq_hist 601 (16, 1, [5; 8; 9],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query602 *)
let HOQ_QUERY602 = slq_hist 602 (16, 1, [6; 8; 9],
  [(nlin_rat "213/100", nlin_rat "81/25"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query603 *)
let HOQ_QUERY603 = slq_hist 603 (16, 1, [7; 8; 9],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query604 *)
let HOQ_QUERY604 = slq_hist 604 (32, 1, [0; 1],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query605 *)
let HOQ_QUERY605 = slq_hist 605 (32, 1, [0; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query606 *)
let HOQ_QUERY606 = slq_hist 606 (32, 1, [1; 2],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query607 *)
let HOQ_QUERY607 = slq_hist 607 (32, 1, [0; 1; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
