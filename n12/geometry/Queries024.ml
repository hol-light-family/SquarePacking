(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries024.lean                          *)
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

(* Lean: query768 *)
let HOQ_QUERY768 = slq_hist 768 (32, 1, [7; 8; 9],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "1543/500", nlin_rat "2")]);;
(* Lean: query769 *)
let HOQ_QUERY769 = slq_hist 769 (192, 1, [0],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query770 *)
let HOQ_QUERY770 = slq_hist 770 (192, 1, [0; 1],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query771 *)
let HOQ_QUERY771 = slq_hist 771 (192, 1, [2],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query772 *)
let HOQ_QUERY772 = slq_hist 772 (192, 1, [0; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query773 *)
let HOQ_QUERY773 = slq_hist 773 (192, 1, [1; 2],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query774 *)
let HOQ_QUERY774 = slq_hist 774 (192, 1, [3],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query775 *)
let HOQ_QUERY775 = slq_hist 775 (192, 1, [0; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query776 *)
let HOQ_QUERY776 = slq_hist 776 (192, 1, [1; 3],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query777 *)
let HOQ_QUERY777 = slq_hist 777 (192, 1, [2; 3],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query778 *)
let HOQ_QUERY778 = slq_hist 778 (192, 1, [0; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query779 *)
let HOQ_QUERY779 = slq_hist 779 (192, 1, [2; 4],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query780 *)
let HOQ_QUERY780 = slq_hist 780 (192, 1, [3; 4],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query781 *)
let HOQ_QUERY781 = slq_hist 781 (192, 1, [5],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query782 *)
let HOQ_QUERY782 = slq_hist 782 (192, 1, [0; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query783 *)
let HOQ_QUERY783 = slq_hist 783 (192, 1, [1; 5],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query784 *)
let HOQ_QUERY784 = slq_hist 784 (192, 1, [2; 5],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query785 *)
let HOQ_QUERY785 = slq_hist 785 (192, 1, [3; 5],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query786 *)
let HOQ_QUERY786 = slq_hist 786 (192, 1, [4; 5],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query787 *)
let HOQ_QUERY787 = slq_hist 787 (192, 1, [6],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query788 *)
let HOQ_QUERY788 = slq_hist 788 (192, 1, [0; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query789 *)
let HOQ_QUERY789 = slq_hist 789 (192, 1, [1; 6],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query790 *)
let HOQ_QUERY790 = slq_hist 790 (192, 1, [2; 6],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query791 *)
let HOQ_QUERY791 = slq_hist 791 (192, 1, [3; 6],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query792 *)
let HOQ_QUERY792 = slq_hist 792 (192, 1, [4; 6],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query793 *)
let HOQ_QUERY793 = slq_hist 793 (192, 1, [5; 6],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query794 *)
let HOQ_QUERY794 = slq_hist 794 (192, 1, [7],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query795 *)
let HOQ_QUERY795 = slq_hist 795 (192, 1, [0; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query796 *)
let HOQ_QUERY796 = slq_hist 796 (192, 1, [1; 7],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query797 *)
let HOQ_QUERY797 = slq_hist 797 (192, 1, [2; 7],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query798 *)
let HOQ_QUERY798 = slq_hist 798 (192, 1, [3; 7],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query799 *)
let HOQ_QUERY799 = slq_hist 799 (192, 1, [4; 7],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
