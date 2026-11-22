(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries020.lean                          *)
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

(* Lean: query640 *)
let HOQ_QUERY640 = slq_hist 640 (32, 1, [1; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query641 *)
let HOQ_QUERY641 = slq_hist 641 (32, 1, [0; 1; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query642 *)
let HOQ_QUERY642 = slq_hist 642 (32, 1, [2; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query643 *)
let HOQ_QUERY643 = slq_hist 643 (32, 1, [0; 2; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query644 *)
let HOQ_QUERY644 = slq_hist 644 (32, 1, [1; 2; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query645 *)
let HOQ_QUERY645 = slq_hist 645 (32, 1, [3; 6],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query646 *)
let HOQ_QUERY646 = slq_hist 646 (32, 1, [0; 3; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query647 *)
let HOQ_QUERY647 = slq_hist 647 (32, 1, [1; 3; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query648 *)
let HOQ_QUERY648 = slq_hist 648 (32, 1, [2; 3; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query649 *)
let HOQ_QUERY649 = slq_hist 649 (32, 1, [4; 6],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query650 *)
let HOQ_QUERY650 = slq_hist 650 (32, 1, [0; 4; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query651 *)
let HOQ_QUERY651 = slq_hist 651 (32, 1, [1; 4; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query652 *)
let HOQ_QUERY652 = slq_hist 652 (32, 1, [2; 4; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query653 *)
let HOQ_QUERY653 = slq_hist 653 (32, 1, [3; 4; 6],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query654 *)
let HOQ_QUERY654 = slq_hist 654 (32, 1, [5; 6],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query655 *)
let HOQ_QUERY655 = slq_hist 655 (32, 1, [0; 5; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query656 *)
let HOQ_QUERY656 = slq_hist 656 (32, 1, [1; 5; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query657 *)
let HOQ_QUERY657 = slq_hist 657 (32, 1, [2; 5; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query658 *)
let HOQ_QUERY658 = slq_hist 658 (32, 1, [3; 5; 6],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query659 *)
let HOQ_QUERY659 = slq_hist 659 (32, 1, [4; 5; 6],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query660 *)
let HOQ_QUERY660 = slq_hist 660 (32, 1, [0; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query661 *)
let HOQ_QUERY661 = slq_hist 661 (32, 1, [1; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query662 *)
let HOQ_QUERY662 = slq_hist 662 (32, 1, [0; 1; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query663 *)
let HOQ_QUERY663 = slq_hist 663 (32, 1, [2; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query664 *)
let HOQ_QUERY664 = slq_hist 664 (32, 1, [0; 2; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query665 *)
let HOQ_QUERY665 = slq_hist 665 (32, 1, [1; 2; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query666 *)
let HOQ_QUERY666 = slq_hist 666 (32, 1, [3; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query667 *)
let HOQ_QUERY667 = slq_hist 667 (32, 1, [0; 3; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query668 *)
let HOQ_QUERY668 = slq_hist 668 (32, 1, [1; 3; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query669 *)
let HOQ_QUERY669 = slq_hist 669 (32, 1, [2; 3; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query670 *)
let HOQ_QUERY670 = slq_hist 670 (32, 1, [4; 7],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query671 *)
let HOQ_QUERY671 = slq_hist 671 (32, 1, [0; 4; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
