(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries021.lean                          *)
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

(* Lean: query672 *)
let HOQ_QUERY672 = slq_hist 672 (32, 1, [1; 4; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query673 *)
let HOQ_QUERY673 = slq_hist 673 (32, 1, [2; 4; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query674 *)
let HOQ_QUERY674 = slq_hist 674 (32, 1, [3; 4; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query675 *)
let HOQ_QUERY675 = slq_hist 675 (32, 1, [5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query676 *)
let HOQ_QUERY676 = slq_hist 676 (32, 1, [0; 5; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query677 *)
let HOQ_QUERY677 = slq_hist 677 (32, 1, [1; 5; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query678 *)
let HOQ_QUERY678 = slq_hist 678 (32, 1, [2; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query679 *)
let HOQ_QUERY679 = slq_hist 679 (32, 1, [3; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query680 *)
let HOQ_QUERY680 = slq_hist 680 (32, 1, [4; 5; 7],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query681 *)
let HOQ_QUERY681 = slq_hist 681 (32, 1, [6; 7],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query682 *)
let HOQ_QUERY682 = slq_hist 682 (32, 1, [0; 6; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query683 *)
let HOQ_QUERY683 = slq_hist 683 (32, 1, [1; 6; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query684 *)
let HOQ_QUERY684 = slq_hist 684 (32, 1, [2; 6; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query685 *)
let HOQ_QUERY685 = slq_hist 685 (32, 1, [3; 6; 7],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query686 *)
let HOQ_QUERY686 = slq_hist 686 (32, 1, [4; 6; 7],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query687 *)
let HOQ_QUERY687 = slq_hist 687 (32, 1, [5; 6; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query688 *)
let HOQ_QUERY688 = slq_hist 688 (32, 1, [0; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query689 *)
let HOQ_QUERY689 = slq_hist 689 (32, 1, [1; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query690 *)
let HOQ_QUERY690 = slq_hist 690 (32, 1, [0; 1; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query691 *)
let HOQ_QUERY691 = slq_hist 691 (32, 1, [2; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query692 *)
let HOQ_QUERY692 = slq_hist 692 (32, 1, [0; 2; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query693 *)
let HOQ_QUERY693 = slq_hist 693 (32, 1, [1; 2; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query694 *)
let HOQ_QUERY694 = slq_hist 694 (32, 1, [3; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query695 *)
let HOQ_QUERY695 = slq_hist 695 (32, 1, [0; 3; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query696 *)
let HOQ_QUERY696 = slq_hist 696 (32, 1, [1; 3; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query697 *)
let HOQ_QUERY697 = slq_hist 697 (32, 1, [2; 3; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query698 *)
let HOQ_QUERY698 = slq_hist 698 (32, 1, [4; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query699 *)
let HOQ_QUERY699 = slq_hist 699 (32, 1, [0; 4; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query700 *)
let HOQ_QUERY700 = slq_hist 700 (32, 1, [1; 4; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query701 *)
let HOQ_QUERY701 = slq_hist 701 (32, 1, [2; 4; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query702 *)
let HOQ_QUERY702 = slq_hist 702 (32, 1, [3; 4; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query703 *)
let HOQ_QUERY703 = slq_hist 703 (32, 1, [5; 8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "72/25")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
