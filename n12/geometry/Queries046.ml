(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries046.lean                          *)
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

(* Lean: query1472 *)
let HOQ_QUERY1472 = slq_hist 1472 (1024, 1, [5; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1473 *)
let HOQ_QUERY1473 = slq_hist 1473 (1024, 1, [7; 8],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1474 *)
let HOQ_QUERY1474 = slq_hist 1474 (1024, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1475 *)
let HOQ_QUERY1475 = slq_hist 1475 (1024, 1, [1; 9],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1476 *)
let HOQ_QUERY1476 = slq_hist 1476 (1024, 1, [2; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1477 *)
let HOQ_QUERY1477 = slq_hist 1477 (1024, 1, [3; 9],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1478 *)
let HOQ_QUERY1478 = slq_hist 1478 (1024, 1, [4; 9],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1479 *)
let HOQ_QUERY1479 = slq_hist 1479 (1024, 1, [5; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1480 *)
let HOQ_QUERY1480 = slq_hist 1480 (1024, 1, [8; 9],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1481 *)
let HOQ_QUERY1481 = slq_hist 1481 (1024, 2, [5; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1482 *)
let HOQ_QUERY1482 = slq_hist 1482 (1024, 2, [3; 5; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1483 *)
let HOQ_QUERY1483 = slq_hist 1483 (1024, 2, [3; 5; 13; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1484 *)
let HOQ_QUERY1484 = slq_hist 1484 (1024, 2, [3; 5; 14; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1485 *)
let HOQ_QUERY1485 = slq_hist 1485 (1024, 2, [3; 5; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1486 *)
let HOQ_QUERY1486 = slq_hist 1486 (1024, 2, [3; 5; 13; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1487 *)
let HOQ_QUERY1487 = slq_hist 1487 (1024, 2, [3; 5; 16; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1488 *)
let HOQ_QUERY1488 = slq_hist 1488 (1024, 2, [3; 5; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1489 *)
let HOQ_QUERY1489 = slq_hist 1489 (1024, 2, [3; 5; 19],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1490 *)
let HOQ_QUERY1490 = slq_hist 1490 (1024, 2, [3; 5; 16; 19],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1491 *)
let HOQ_QUERY1491 = slq_hist 1491 (1024, 2, [3; 5; 17; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1492 *)
let HOQ_QUERY1492 = slq_hist 1492 (1024, 2, [4; 5; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1493 *)
let HOQ_QUERY1493 = slq_hist 1493 (1024, 2, [4; 5; 13; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1494 *)
let HOQ_QUERY1494 = slq_hist 1494 (1024, 2, [4; 5; 14; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1495 *)
let HOQ_QUERY1495 = slq_hist 1495 (1024, 2, [4; 5; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1496 *)
let HOQ_QUERY1496 = slq_hist 1496 (1024, 2, [4; 5; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1497 *)
let HOQ_QUERY1497 = slq_hist 1497 (1024, 2, [4; 5; 17; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1498 *)
let HOQ_QUERY1498 = slq_hist 1498 (1024, 2, [7; 13; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1499 *)
let HOQ_QUERY1499 = slq_hist 1499 (1024, 2, [7; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1500 *)
let HOQ_QUERY1500 = slq_hist 1500 (1024, 2, [7; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1501 *)
let HOQ_QUERY1501 = slq_hist 1501 (1024, 2, [7; 14; 17],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1502 *)
let HOQ_QUERY1502 = slq_hist 1502 (1024, 2, [7; 16; 18],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1503 *)
let HOQ_QUERY1503 = slq_hist 1503 (1024, 2, [5; 7; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
