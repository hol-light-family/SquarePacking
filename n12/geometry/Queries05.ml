(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Queries05.lean                     *)
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

(* Lean: query976_629 *)
let C981DSQ_QUERY976_629 = slq_new (1024, 1, [5; 6],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query976_630 *)
let C981DSQ_QUERY976_630 = slq_new (1024, 1, [0; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_631 *)
let C981DSQ_QUERY976_631 = slq_new (1024, 1, [1; 7],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_632 *)
let C981DSQ_QUERY976_632 = slq_new (1024, 1, [2; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query976_633 *)
let C981DSQ_QUERY976_633 = slq_new (1024, 1, [5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_634 *)
let C981DSQ_QUERY976_634 = slq_new (1024, 1, [8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_635 *)
let C981DSQ_QUERY976_635 = slq_new (1024, 1, [0; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_636 *)
let C981DSQ_QUERY976_636 = slq_new (1024, 1, [1; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_637 *)
let C981DSQ_QUERY976_637 = slq_new (1024, 1, [2; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_638 *)
let C981DSQ_QUERY976_638 = slq_new (1024, 1, [3; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_639 *)
let C981DSQ_QUERY976_639 = slq_new (1024, 1, [4; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_640 *)
let C981DSQ_QUERY976_640 = slq_new (1024, 1, [5; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_641 *)
let C981DSQ_QUERY976_641 = slq_new (1024, 1, [7; 8],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_642 *)
let C981DSQ_QUERY976_642 = slq_new (1024, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query976_643 *)
let C981DSQ_QUERY976_643 = slq_new (1024, 1, [1; 9],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_644 *)
let C981DSQ_QUERY976_644 = slq_new (1024, 1, [2; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_645 *)
let C981DSQ_QUERY976_645 = slq_new (1024, 1, [3; 9],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_646 *)
let C981DSQ_QUERY976_646 = slq_new (1024, 1, [4; 9],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_647 *)
let C981DSQ_QUERY976_647 = slq_new (1024, 1, [5; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_648 *)
let C981DSQ_QUERY976_648 = slq_new (1024, 1, [8; 9],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_649 *)
let C981DSQ_QUERY976_649 = slq_new (1024, 2, [5; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_650 *)
let C981DSQ_QUERY976_650 = slq_new (1024, 2, [3; 5; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_651 *)
let C981DSQ_QUERY976_651 = slq_new (1024, 2, [3; 5; 13; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_652 *)
let C981DSQ_QUERY976_652 = slq_new (1024, 2, [3; 5; 14; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_653 *)
let C981DSQ_QUERY976_653 = slq_new (1024, 2, [3; 5; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
