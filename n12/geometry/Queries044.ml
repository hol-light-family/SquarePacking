(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries044.lean *)
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

(* Lean: query1408 *)
let HOQ_QUERY1408 = slq_hist 1408 (1024, 0, [0; 2],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1409 *)
let HOQ_QUERY1409 = slq_hist 1409 (1024, 0, [1; 2],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1410 *)
let HOQ_QUERY1410 = slq_hist 1410 (1024, 0, [0; 3],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1411 *)
let HOQ_QUERY1411 = slq_hist 1411 (1024, 0, [1; 3],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1412 *)
let HOQ_QUERY1412 = slq_hist 1412 (1024, 0, [2; 3],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1413 *)
let HOQ_QUERY1413 = slq_hist 1413 (1024, 0, [0; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1414 *)
let HOQ_QUERY1414 = slq_hist 1414 (1024, 0, [1; 4],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1415 *)
let HOQ_QUERY1415 = slq_hist 1415 (1024, 0, [2; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1416 *)
let HOQ_QUERY1416 = slq_hist 1416 (1024, 0, [3; 4],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1417 *)
let HOQ_QUERY1417 = slq_hist 1417 (1024, 0, [0; 5],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1418 *)
let HOQ_QUERY1418 = slq_hist 1418 (1024, 0, [1; 5],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1419 *)
let HOQ_QUERY1419 = slq_hist 1419 (1024, 0, [2; 5],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1420 *)
let HOQ_QUERY1420 = slq_hist 1420 (1024, 0, [0; 6],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1421 *)
let HOQ_QUERY1421 = slq_hist 1421 (1024, 0, [1; 6],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1422 *)
let HOQ_QUERY1422 = slq_hist 1422 (1024, 0, [2; 6],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1423 *)
let HOQ_QUERY1423 = slq_hist 1423 (1024, 0, [3; 6],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1424 *)
let HOQ_QUERY1424 = slq_hist 1424 (1024, 0, [4; 6],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1425 *)
let HOQ_QUERY1425 = slq_hist 1425 (1024, 0, [5; 6],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1426 *)
let HOQ_QUERY1426 = slq_hist 1426 (1024, 0, [0; 7],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1427 *)
let HOQ_QUERY1427 = slq_hist 1427 (1024, 0, [1; 7],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1428 *)
let HOQ_QUERY1428 = slq_hist 1428 (1024, 0, [2; 7],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1429 *)
let HOQ_QUERY1429 = slq_hist 1429 (1024, 0, [3; 7],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1430 *)
let HOQ_QUERY1430 = slq_hist 1430 (1024, 0, [4; 7],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1431 *)
let HOQ_QUERY1431 = slq_hist 1431 (1024, 0, [6; 7],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1432 *)
let HOQ_QUERY1432 = slq_hist 1432 (1024, 0, [0; 8],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1433 *)
let HOQ_QUERY1433 = slq_hist 1433 (1024, 0, [1; 8],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1434 *)
let HOQ_QUERY1434 = slq_hist 1434 (1024, 0, [2; 8],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1435 *)
let HOQ_QUERY1435 = slq_hist 1435 (1024, 0, [3; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1436 *)
let HOQ_QUERY1436 = slq_hist 1436 (1024, 0, [4; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1437 *)
let HOQ_QUERY1437 = slq_hist 1437 (1024, 0, [6; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1438 *)
let HOQ_QUERY1438 = slq_hist 1438 (1024, 0, [7; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1439 *)
let HOQ_QUERY1439 = slq_hist 1439 (1024, 0, [0; 9],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
