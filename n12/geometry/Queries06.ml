(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Queries06.lean                     *)
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

(* Lean: query976_654 *)
let C981DSQ_QUERY976_654 = slq_new (1024, 2, [3; 5; 13; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query976_655 *)
let C981DSQ_QUERY976_655 = slq_new (1024, 2, [3; 5; 16; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query976_656 *)
let C981DSQ_QUERY976_656 = slq_new (1024, 2, [3; 5; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_657 *)
let C981DSQ_QUERY976_657 = slq_new (1024, 2, [3; 5; 19],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_658 *)
let C981DSQ_QUERY976_658 = slq_new (1024, 2, [3; 5; 16; 19],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_659 *)
let C981DSQ_QUERY976_659 = slq_new (1024, 2, [3; 5; 17; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query976_660 *)
let C981DSQ_QUERY976_660 = slq_new (1024, 2, [4; 5; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_661 *)
let C981DSQ_QUERY976_661 = slq_new (1024, 2, [4; 5; 13; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_662 *)
let C981DSQ_QUERY976_662 = slq_new (1024, 2, [4; 5; 14; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_663 *)
let C981DSQ_QUERY976_663 = slq_new (1024, 2, [4; 5; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_664 *)
let C981DSQ_QUERY976_664 = slq_new (1024, 2, [4; 5; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_665 *)
let C981DSQ_QUERY976_665 = slq_new (1024, 2, [4; 5; 17; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_666 *)
let C981DSQ_QUERY976_666 = slq_new (1024, 2, [7; 13; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_667 *)
let C981DSQ_QUERY976_667 = slq_new (1024, 2, [7; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query976_668 *)
let C981DSQ_QUERY976_668 = slq_new (1024, 2, [7; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_669 *)
let C981DSQ_QUERY976_669 = slq_new (1024, 2, [7; 14; 17],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_670 *)
let C981DSQ_QUERY976_670 = slq_new (1024, 2, [7; 16; 18],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_671 *)
let C981DSQ_QUERY976_671 = slq_new (1024, 2, [5; 7; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query976_672 *)
let C981DSQ_QUERY976_672 = slq_new (1024, 2, [5; 7; 16; 18],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_673 *)
let C981DSQ_QUERY976_673 = slq_new (1024, 2, [5; 8; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_674 *)
let C981DSQ_QUERY976_674 = slq_new (1024, 2, [5; 8; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_675 *)
let C981DSQ_QUERY976_675 = slq_new (1024, 2, [5; 8; 14; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_676 *)
let C981DSQ_QUERY976_676 = slq_new (1024, 2, [5; 8; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_677 *)
let C981DSQ_QUERY976_677 = slq_new (1024, 2, [5; 8; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query976_678 *)
let C981DSQ_QUERY976_678 = slq_new (1024, 2, [5; 8; 16; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
