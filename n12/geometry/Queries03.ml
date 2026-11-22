(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Queries03.lean                     *)
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

(* Lean: query976_579 *)
let C981DSQ_QUERY976_579 = slq_new (1024, 0, [6],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_580 *)
let C981DSQ_QUERY976_580 = slq_new (1024, 0, [0; 6],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query976_581 *)
let C981DSQ_QUERY976_581 = slq_new (1024, 0, [1; 6],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query976_582 *)
let C981DSQ_QUERY976_582 = slq_new (1024, 0, [2; 6],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_583 *)
let C981DSQ_QUERY976_583 = slq_new (1024, 0, [3; 6],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_584 *)
let C981DSQ_QUERY976_584 = slq_new (1024, 0, [4; 6],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_585 *)
let C981DSQ_QUERY976_585 = slq_new (1024, 0, [5; 6],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_586 *)
let C981DSQ_QUERY976_586 = slq_new (1024, 0, [0; 7],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_587 *)
let C981DSQ_QUERY976_587 = slq_new (1024, 0, [1; 7],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query976_588 *)
let C981DSQ_QUERY976_588 = slq_new (1024, 0, [2; 7],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query976_589 *)
let C981DSQ_QUERY976_589 = slq_new (1024, 0, [3; 7],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_590 *)
let C981DSQ_QUERY976_590 = slq_new (1024, 0, [4; 7],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_591 *)
let C981DSQ_QUERY976_591 = slq_new (1024, 0, [6; 7],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_592 *)
let C981DSQ_QUERY976_592 = slq_new (1024, 0, [8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_593 *)
let C981DSQ_QUERY976_593 = slq_new (1024, 0, [0; 8],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query976_594 *)
let C981DSQ_QUERY976_594 = slq_new (1024, 0, [1; 8],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_595 *)
let C981DSQ_QUERY976_595 = slq_new (1024, 0, [2; 8],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query976_596 *)
let C981DSQ_QUERY976_596 = slq_new (1024, 0, [3; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_597 *)
let C981DSQ_QUERY976_597 = slq_new (1024, 0, [4; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_598 *)
let C981DSQ_QUERY976_598 = slq_new (1024, 0, [6; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_599 *)
let C981DSQ_QUERY976_599 = slq_new (1024, 0, [7; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_600 *)
let C981DSQ_QUERY976_600 = slq_new (1024, 0, [0; 9],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query976_601 *)
let C981DSQ_QUERY976_601 = slq_new (1024, 0, [1; 9],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_602 *)
let C981DSQ_QUERY976_602 = slq_new (1024, 0, [2; 9],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query976_603 *)
let C981DSQ_QUERY976_603 = slq_new (1024, 0, [3; 9],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
