(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries048.lean                          *)
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

(* Lean: query1536 *)
let HOQ_QUERY1536 = slq_hist 1536 (1024, 2, [8; 9; 19],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1537 *)
let HOQ_QUERY1537 = slq_hist 1537 (1024, 2, [8; 9; 17; 19],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1538 *)
let HOQ_QUERY1538 = slq_hist 1538 (33792, 0, [0],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1539 *)
let HOQ_QUERY1539 = slq_hist 1539 (33792, 0, [1],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1540 *)
let HOQ_QUERY1540 = slq_hist 1540 (33792, 0, [0; 1],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1541 *)
let HOQ_QUERY1541 = slq_hist 1541 (33792, 0, [2],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1542 *)
let HOQ_QUERY1542 = slq_hist 1542 (33792, 0, [0; 2],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1543 *)
let HOQ_QUERY1543 = slq_hist 1543 (33792, 0, [1; 2],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1544 *)
let HOQ_QUERY1544 = slq_hist 1544 (33792, 0, [0; 3],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1545 *)
let HOQ_QUERY1545 = slq_hist 1545 (33792, 0, [1; 3],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1546 *)
let HOQ_QUERY1546 = slq_hist 1546 (33792, 0, [2; 3],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1547 *)
let HOQ_QUERY1547 = slq_hist 1547 (33792, 0, [4],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1548 *)
let HOQ_QUERY1548 = slq_hist 1548 (33792, 0, [0; 4],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1549 *)
let HOQ_QUERY1549 = slq_hist 1549 (33792, 0, [1; 4],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1550 *)
let HOQ_QUERY1550 = slq_hist 1550 (33792, 0, [2; 4],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1551 *)
let HOQ_QUERY1551 = slq_hist 1551 (33792, 0, [3; 4],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1552 *)
let HOQ_QUERY1552 = slq_hist 1552 (33792, 0, [0; 5],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1553 *)
let HOQ_QUERY1553 = slq_hist 1553 (33792, 0, [1; 5],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1554 *)
let HOQ_QUERY1554 = slq_hist 1554 (33792, 0, [2; 5],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1555 *)
let HOQ_QUERY1555 = slq_hist 1555 (33792, 0, [6],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1556 *)
let HOQ_QUERY1556 = slq_hist 1556 (33792, 0, [0; 6],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1557 *)
let HOQ_QUERY1557 = slq_hist 1557 (33792, 0, [1; 6],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1558 *)
let HOQ_QUERY1558 = slq_hist 1558 (33792, 0, [2; 6],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1559 *)
let HOQ_QUERY1559 = slq_hist 1559 (33792, 0, [3; 6],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1560 *)
let HOQ_QUERY1560 = slq_hist 1560 (33792, 0, [4; 6],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1561 *)
let HOQ_QUERY1561 = slq_hist 1561 (33792, 0, [5; 6],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1562 *)
let HOQ_QUERY1562 = slq_hist 1562 (33792, 0, [0; 7],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1563 *)
let HOQ_QUERY1563 = slq_hist 1563 (33792, 0, [1; 7],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1564 *)
let HOQ_QUERY1564 = slq_hist 1564 (33792, 0, [2; 7],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1565 *)
let HOQ_QUERY1565 = slq_hist 1565 (33792, 0, [4; 7],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1566 *)
let HOQ_QUERY1566 = slq_hist 1566 (33792, 0, [6; 7],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1567 *)
let HOQ_QUERY1567 = slq_hist 1567 (33792, 0, [8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
