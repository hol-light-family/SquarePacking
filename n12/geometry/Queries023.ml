(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries023.lean                          *)
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

(* Lean: query736 *)
let HOQ_QUERY736 = slq_hist 736 (32, 1, [1; 4; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query737 *)
let HOQ_QUERY737 = slq_hist 737 (32, 1, [2; 4; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query738 *)
let HOQ_QUERY738 = slq_hist 738 (32, 1, [3; 4; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query739 *)
let HOQ_QUERY739 = slq_hist 739 (32, 1, [5; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2")]);;
(* Lean: query740 *)
let HOQ_QUERY740 = slq_hist 740 (32, 1, [0; 5; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query741 *)
let HOQ_QUERY741 = slq_hist 741 (32, 1, [1; 5; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query742 *)
let HOQ_QUERY742 = slq_hist 742 (32, 1, [2; 5; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query743 *)
let HOQ_QUERY743 = slq_hist 743 (32, 1, [3; 5; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query744 *)
let HOQ_QUERY744 = slq_hist 744 (32, 1, [4; 5; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query745 *)
let HOQ_QUERY745 = slq_hist 745 (32, 1, [6; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query746 *)
let HOQ_QUERY746 = slq_hist 746 (32, 1, [0; 6; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query747 *)
let HOQ_QUERY747 = slq_hist 747 (32, 1, [1; 6; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query748 *)
let HOQ_QUERY748 = slq_hist 748 (32, 1, [2; 6; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query749 *)
let HOQ_QUERY749 = slq_hist 749 (32, 1, [3; 6; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query750 *)
let HOQ_QUERY750 = slq_hist 750 (32, 1, [4; 6; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query751 *)
let HOQ_QUERY751 = slq_hist 751 (32, 1, [5; 6; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query752 *)
let HOQ_QUERY752 = slq_hist 752 (32, 1, [7; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query753 *)
let HOQ_QUERY753 = slq_hist 753 (32, 1, [0; 7; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query754 *)
let HOQ_QUERY754 = slq_hist 754 (32, 1, [1; 7; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query755 *)
let HOQ_QUERY755 = slq_hist 755 (32, 1, [2; 7; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query756 *)
let HOQ_QUERY756 = slq_hist 756 (32, 1, [3; 7; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query757 *)
let HOQ_QUERY757 = slq_hist 757 (32, 1, [4; 7; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query758 *)
let HOQ_QUERY758 = slq_hist 758 (32, 1, [5; 7; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query759 *)
let HOQ_QUERY759 = slq_hist 759 (32, 1, [6; 7; 9],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query760 *)
let HOQ_QUERY760 = slq_hist 760 (32, 1, [8; 9],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2")]);;
(* Lean: query761 *)
let HOQ_QUERY761 = slq_hist 761 (32, 1, [0; 8; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query762 *)
let HOQ_QUERY762 = slq_hist 762 (32, 1, [1; 8; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query763 *)
let HOQ_QUERY763 = slq_hist 763 (32, 1, [2; 8; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query764 *)
let HOQ_QUERY764 = slq_hist 764 (32, 1, [3; 8; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query765 *)
let HOQ_QUERY765 = slq_hist 765 (32, 1, [4; 8; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query766 *)
let HOQ_QUERY766 = slq_hist 766 (32, 1, [5; 8; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2")]);;
(* Lean: query767 *)
let HOQ_QUERY767 = slq_hist 767 (32, 1, [6; 8; 9],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "1543/500", nlin_rat "2")]);;
