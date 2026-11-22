(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Queries08.lean                     *)
(* (N12Compact.C981DomainSubset): exact inherited local queries, registered *)
(* with slq_new (SharedLocalQueries.ml) and re-proved by the kernel from    *)
(* their inside / outside points.  Both are .four queries with transform    *)
(* (swap, reflect x, reflect y) = (false, true, true) of fourDatum64 =      *)
(* <A (1,8/5), B (1,113/50), P (457/500,2), E (87/50,2)>, i.e. the points    *)
(* x -> 4 - x, y -> 4 - y: A, B inside, P, E outside (as in Queries01.ml).  *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query976_704 *)
let C981DSQ_QUERY976_704 = slq_new (1024, 2, [8; 9; 19],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query976_705 *)
let C981DSQ_QUERY976_705 = slq_new (1024, 2, [8; 9; 17; 19],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
