(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Queries04.lean                     *)
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

(* Lean: query976_604 *)
let C981DSQ_QUERY976_604 = slq_new (1024, 0, [6; 9],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_605 *)
let C981DSQ_QUERY976_605 = slq_new (1024, 1, [0],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_606 *)
let C981DSQ_QUERY976_606 = slq_new (1024, 1, [1],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_607 *)
let C981DSQ_QUERY976_607 = slq_new (1024, 1, [0; 1],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_608 *)
let C981DSQ_QUERY976_608 = slq_new (1024, 1, [2],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query976_609 *)
let C981DSQ_QUERY976_609 = slq_new (1024, 1, [0; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_610 *)
let C981DSQ_QUERY976_610 = slq_new (1024, 1, [1; 2],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_611 *)
let C981DSQ_QUERY976_611 = slq_new (1024, 1, [3],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_612 *)
let C981DSQ_QUERY976_612 = slq_new (1024, 1, [0; 3],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_613 *)
let C981DSQ_QUERY976_613 = slq_new (1024, 1, [1; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_614 *)
let C981DSQ_QUERY976_614 = slq_new (1024, 1, [2; 3],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_615 *)
let C981DSQ_QUERY976_615 = slq_new (1024, 1, [4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_616 *)
let C981DSQ_QUERY976_616 = slq_new (1024, 1, [0; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_617 *)
let C981DSQ_QUERY976_617 = slq_new (1024, 1, [1; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_618 *)
let C981DSQ_QUERY976_618 = slq_new (1024, 1, [2; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query976_619 *)
let C981DSQ_QUERY976_619 = slq_new (1024, 1, [3; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_620 *)
let C981DSQ_QUERY976_620 = slq_new (1024, 1, [5],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_621 *)
let C981DSQ_QUERY976_621 = slq_new (1024, 1, [0; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_622 *)
let C981DSQ_QUERY976_622 = slq_new (1024, 1, [1; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_623 *)
let C981DSQ_QUERY976_623 = slq_new (1024, 1, [2; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_624 *)
let C981DSQ_QUERY976_624 = slq_new (1024, 1, [3; 5],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_625 *)
let C981DSQ_QUERY976_625 = slq_new (1024, 1, [4; 5],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_626 *)
let C981DSQ_QUERY976_626 = slq_new (1024, 1, [0; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query976_627 *)
let C981DSQ_QUERY976_627 = slq_new (1024, 1, [1; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_628 *)
let C981DSQ_QUERY976_628 = slq_new (1024, 1, [2; 6],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
