(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Queries07.lean                     *)
(* (N12Compact.C981DomainSubset): exact inherited local queries.  Each Lean *)
(* checked_local_query is registered with slq_new (SharedLocalQueries.ml):  *)
(* the HOL kernel re-proves the query from its inside / outside points     *)
(* (a .hull query: its three hull points inside, its fourth point outside; *)
(* a .four query: the transformed FourPointDatum A, B inside, P, E outside; *)
(* a .short query: its cluster points inside, the pattern points outside).  *)
(* C981DSQ_QUERY976_N : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>  *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query976_679 *)
let C981DSQ_QUERY976_679 = slq_new (1024, 2, [5; 8; 17; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query976_680 *)
let C981DSQ_QUERY976_680 = slq_new (1024, 2, [9; 13; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_681 *)
let C981DSQ_QUERY976_681 = slq_new (1024, 2, [9; 14; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_682 *)
let C981DSQ_QUERY976_682 = slq_new (1024, 2, [9; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_683 *)
let C981DSQ_QUERY976_683 = slq_new (1024, 2, [9; 14; 17],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_684 *)
let C981DSQ_QUERY976_684 = slq_new (1024, 2, [9; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query976_685 *)
let C981DSQ_QUERY976_685 = slq_new (1024, 2, [4; 9; 13; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_686 *)
let C981DSQ_QUERY976_686 = slq_new (1024, 2, [4; 9; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_687 *)
let C981DSQ_QUERY976_687 = slq_new (1024, 2, [4; 9; 17],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_688 *)
let C981DSQ_QUERY976_688 = slq_new (1024, 2, [4; 9; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_689 *)
let C981DSQ_QUERY976_689 = slq_new (1024, 2, [4; 9; 14; 17],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_690 *)
let C981DSQ_QUERY976_690 = slq_new (1024, 2, [4; 9; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query976_691 *)
let C981DSQ_QUERY976_691 = slq_new (1024, 2, [4; 9; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_692 *)
let C981DSQ_QUERY976_692 = slq_new (1024, 2, [4; 9; 17; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_693 *)
let C981DSQ_QUERY976_693 = slq_new (1024, 2, [5; 9; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query976_694 *)
let C981DSQ_QUERY976_694 = slq_new (1024, 2, [7; 9; 13; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_695 *)
let C981DSQ_QUERY976_695 = slq_new (1024, 2, [7; 9; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query976_696 *)
let C981DSQ_QUERY976_696 = slq_new (1024, 2, [7; 9; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_697 *)
let C981DSQ_QUERY976_697 = slq_new (1024, 2, [7; 9; 14; 17],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_698 *)
let C981DSQ_QUERY976_698 = slq_new (1024, 2, [7; 9; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query976_699 *)
let C981DSQ_QUERY976_699 = slq_new (1024, 2, [8; 9; 13; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_700 *)
let C981DSQ_QUERY976_700 = slq_new (1024, 2, [8; 9; 14; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_701 *)
let C981DSQ_QUERY976_701 = slq_new (1024, 2, [8; 9; 17],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_702 *)
let C981DSQ_QUERY976_702 = slq_new (1024, 2, [8; 9; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_703 *)
let C981DSQ_QUERY976_703 = slq_new (1024, 2, [8; 9; 14; 17],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
