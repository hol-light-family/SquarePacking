(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries045.lean *)
(* (N12Compact.HistoricalOwnership.Queries): exact inherited local queries.  Each Lean *)
(* checked_local_query is registered with slq_hist n (SharedLocalQueries.ml):*)
(* the HOL kernel re-proves the query from its inside / outside points     *)
(* (a .hull query: its three hull points inside, its fourth point outside; *)
(* a .four query: the transformed FourPointDatum A, B inside, P, E outside; *)
(* a .short query: its cluster points inside, the pattern points outside).  *)
(* HOQ_QUERYn : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>  *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query1440 *)
let HOQ_QUERY1440 = slq_hist 1440 (1024, 0, [1; 9],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1441 *)
let HOQ_QUERY1441 = slq_hist 1441 (1024, 0, [2; 9],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1442 *)
let HOQ_QUERY1442 = slq_hist 1442 (1024, 0, [3; 9],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1443 *)
let HOQ_QUERY1443 = slq_hist 1443 (1024, 0, [6; 9],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1444 *)
let HOQ_QUERY1444 = slq_hist 1444 (1024, 1, [0; 1],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1445 *)
let HOQ_QUERY1445 = slq_hist 1445 (1024, 1, [0; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1446 *)
let HOQ_QUERY1446 = slq_hist 1446 (1024, 1, [1; 2],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1447 *)
let HOQ_QUERY1447 = slq_hist 1447 (1024, 1, [0; 3],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1448 *)
let HOQ_QUERY1448 = slq_hist 1448 (1024, 1, [1; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1449 *)
let HOQ_QUERY1449 = slq_hist 1449 (1024, 1, [2; 3],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1450 *)
let HOQ_QUERY1450 = slq_hist 1450 (1024, 1, [0; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1451 *)
let HOQ_QUERY1451 = slq_hist 1451 (1024, 1, [1; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1452 *)
let HOQ_QUERY1452 = slq_hist 1452 (1024, 1, [2; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1453 *)
let HOQ_QUERY1453 = slq_hist 1453 (1024, 1, [3; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1454 *)
let HOQ_QUERY1454 = slq_hist 1454 (1024, 1, [0; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1455 *)
let HOQ_QUERY1455 = slq_hist 1455 (1024, 1, [1; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1456 *)
let HOQ_QUERY1456 = slq_hist 1456 (1024, 1, [2; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1457 *)
let HOQ_QUERY1457 = slq_hist 1457 (1024, 1, [3; 5],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1458 *)
let HOQ_QUERY1458 = slq_hist 1458 (1024, 1, [4; 5],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1459 *)
let HOQ_QUERY1459 = slq_hist 1459 (1024, 1, [0; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1460 *)
let HOQ_QUERY1460 = slq_hist 1460 (1024, 1, [1; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1461 *)
let HOQ_QUERY1461 = slq_hist 1461 (1024, 1, [2; 6],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1462 *)
let HOQ_QUERY1462 = slq_hist 1462 (1024, 1, [5; 6],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1463 *)
let HOQ_QUERY1463 = slq_hist 1463 (1024, 1, [0; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1464 *)
let HOQ_QUERY1464 = slq_hist 1464 (1024, 1, [1; 7],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1465 *)
let HOQ_QUERY1465 = slq_hist 1465 (1024, 1, [2; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1466 *)
let HOQ_QUERY1466 = slq_hist 1466 (1024, 1, [5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1467 *)
let HOQ_QUERY1467 = slq_hist 1467 (1024, 1, [0; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1468 *)
let HOQ_QUERY1468 = slq_hist 1468 (1024, 1, [1; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1469 *)
let HOQ_QUERY1469 = slq_hist 1469 (1024, 1, [2; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1470 *)
let HOQ_QUERY1470 = slq_hist 1470 (1024, 1, [3; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1471 *)
let HOQ_QUERY1471 = slq_hist 1471 (1024, 1, [4; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
