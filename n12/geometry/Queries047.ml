(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries047.lean                          *)
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

(* Lean: query1504 *)
let HOQ_QUERY1504 = slq_hist 1504 (1024, 2, [5; 7; 16; 18],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1505 *)
let HOQ_QUERY1505 = slq_hist 1505 (1024, 2, [5; 8; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1506 *)
let HOQ_QUERY1506 = slq_hist 1506 (1024, 2, [5; 8; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1507 *)
let HOQ_QUERY1507 = slq_hist 1507 (1024, 2, [5; 8; 14; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1508 *)
let HOQ_QUERY1508 = slq_hist 1508 (1024, 2, [5; 8; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1509 *)
let HOQ_QUERY1509 = slq_hist 1509 (1024, 2, [5; 8; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query1510 *)
let HOQ_QUERY1510 = slq_hist 1510 (1024, 2, [5; 8; 16; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query1511 *)
let HOQ_QUERY1511 = slq_hist 1511 (1024, 2, [5; 8; 17; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query1512 *)
let HOQ_QUERY1512 = slq_hist 1512 (1024, 2, [9; 13; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1513 *)
let HOQ_QUERY1513 = slq_hist 1513 (1024, 2, [9; 14; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1514 *)
let HOQ_QUERY1514 = slq_hist 1514 (1024, 2, [9; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1515 *)
let HOQ_QUERY1515 = slq_hist 1515 (1024, 2, [9; 14; 17],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1516 *)
let HOQ_QUERY1516 = slq_hist 1516 (1024, 2, [9; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query1517 *)
let HOQ_QUERY1517 = slq_hist 1517 (1024, 2, [4; 9; 13; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1518 *)
let HOQ_QUERY1518 = slq_hist 1518 (1024, 2, [4; 9; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1519 *)
let HOQ_QUERY1519 = slq_hist 1519 (1024, 2, [4; 9; 17],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1520 *)
let HOQ_QUERY1520 = slq_hist 1520 (1024, 2, [4; 9; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1521 *)
let HOQ_QUERY1521 = slq_hist 1521 (1024, 2, [4; 9; 14; 17],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1522 *)
let HOQ_QUERY1522 = slq_hist 1522 (1024, 2, [4; 9; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query1523 *)
let HOQ_QUERY1523 = slq_hist 1523 (1024, 2, [4; 9; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1524 *)
let HOQ_QUERY1524 = slq_hist 1524 (1024, 2, [4; 9; 17; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1525 *)
let HOQ_QUERY1525 = slq_hist 1525 (1024, 2, [5; 9; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query1526 *)
let HOQ_QUERY1526 = slq_hist 1526 (1024, 2, [7; 9; 13; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1527 *)
let HOQ_QUERY1527 = slq_hist 1527 (1024, 2, [7; 9; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1528 *)
let HOQ_QUERY1528 = slq_hist 1528 (1024, 2, [7; 9; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1529 *)
let HOQ_QUERY1529 = slq_hist 1529 (1024, 2, [7; 9; 14; 17],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1530 *)
let HOQ_QUERY1530 = slq_hist 1530 (1024, 2, [7; 9; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query1531 *)
let HOQ_QUERY1531 = slq_hist 1531 (1024, 2, [8; 9; 13; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1532 *)
let HOQ_QUERY1532 = slq_hist 1532 (1024, 2, [8; 9; 14; 16],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1533 *)
let HOQ_QUERY1533 = slq_hist 1533 (1024, 2, [8; 9; 17],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1534 *)
let HOQ_QUERY1534 = slq_hist 1534 (1024, 2, [8; 9; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1535 *)
let HOQ_QUERY1535 = slq_hist 1535 (1024, 2, [8; 9; 14; 17],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
