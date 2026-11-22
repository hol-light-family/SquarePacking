(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries019.lean                          *)
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

(* Lean: query608 *)
let HOQ_QUERY608 = slq_hist 608 (32, 1, [0; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query609 *)
let HOQ_QUERY609 = slq_hist 609 (32, 1, [1; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query610 *)
let HOQ_QUERY610 = slq_hist 610 (32, 1, [0; 1; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query611 *)
let HOQ_QUERY611 = slq_hist 611 (32, 1, [2; 3],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query612 *)
let HOQ_QUERY612 = slq_hist 612 (32, 1, [0; 2; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query613 *)
let HOQ_QUERY613 = slq_hist 613 (32, 1, [1; 2; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query614 *)
let HOQ_QUERY614 = slq_hist 614 (32, 1, [0; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query615 *)
let HOQ_QUERY615 = slq_hist 615 (32, 1, [1; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query616 *)
let HOQ_QUERY616 = slq_hist 616 (32, 1, [0; 1; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query617 *)
let HOQ_QUERY617 = slq_hist 617 (32, 1, [2; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query618 *)
let HOQ_QUERY618 = slq_hist 618 (32, 1, [0; 2; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query619 *)
let HOQ_QUERY619 = slq_hist 619 (32, 1, [1; 2; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query620 *)
let HOQ_QUERY620 = slq_hist 620 (32, 1, [3; 4],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query621 *)
let HOQ_QUERY621 = slq_hist 621 (32, 1, [0; 3; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query622 *)
let HOQ_QUERY622 = slq_hist 622 (32, 1, [1; 3; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query623 *)
let HOQ_QUERY623 = slq_hist 623 (32, 1, [2; 3; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query624 *)
let HOQ_QUERY624 = slq_hist 624 (32, 1, [0; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query625 *)
let HOQ_QUERY625 = slq_hist 625 (32, 1, [1; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query626 *)
let HOQ_QUERY626 = slq_hist 626 (32, 1, [0; 1; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query627 *)
let HOQ_QUERY627 = slq_hist 627 (32, 1, [2; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query628 *)
let HOQ_QUERY628 = slq_hist 628 (32, 1, [0; 2; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query629 *)
let HOQ_QUERY629 = slq_hist 629 (32, 1, [1; 2; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query630 *)
let HOQ_QUERY630 = slq_hist 630 (32, 1, [3; 5],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query631 *)
let HOQ_QUERY631 = slq_hist 631 (32, 1, [0; 3; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query632 *)
let HOQ_QUERY632 = slq_hist 632 (32, 1, [1; 3; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query633 *)
let HOQ_QUERY633 = slq_hist 633 (32, 1, [2; 3; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query634 *)
let HOQ_QUERY634 = slq_hist 634 (32, 1, [4; 5],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query635 *)
let HOQ_QUERY635 = slq_hist 635 (32, 1, [0; 4; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query636 *)
let HOQ_QUERY636 = slq_hist 636 (32, 1, [1; 4; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query637 *)
let HOQ_QUERY637 = slq_hist 637 (32, 1, [2; 4; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query638 *)
let HOQ_QUERY638 = slq_hist 638 (32, 1, [3; 4; 5],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query639 *)
let HOQ_QUERY639 = slq_hist 639 (32, 1, [0; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
