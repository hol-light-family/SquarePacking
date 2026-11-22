(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries049.lean                          *)
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

(* Lean: query1568 *)
let HOQ_QUERY1568 = slq_hist 1568 (33792, 0, [0; 8],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1569 *)
let HOQ_QUERY1569 = slq_hist 1569 (33792, 0, [1; 8],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1570 *)
let HOQ_QUERY1570 = slq_hist 1570 (33792, 0, [2; 8],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1571 *)
let HOQ_QUERY1571 = slq_hist 1571 (33792, 0, [3; 8],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1572 *)
let HOQ_QUERY1572 = slq_hist 1572 (33792, 0, [4; 8],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1573 *)
let HOQ_QUERY1573 = slq_hist 1573 (33792, 0, [6; 8],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1574 *)
let HOQ_QUERY1574 = slq_hist 1574 (33792, 0, [7; 8],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1575 *)
let HOQ_QUERY1575 = slq_hist 1575 (33792, 0, [9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1576 *)
let HOQ_QUERY1576 = slq_hist 1576 (33792, 0, [0; 9],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1577 *)
let HOQ_QUERY1577 = slq_hist 1577 (33792, 0, [1; 9],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1578 *)
let HOQ_QUERY1578 = slq_hist 1578 (33792, 0, [2; 9],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1579 *)
let HOQ_QUERY1579 = slq_hist 1579 (33792, 0, [3; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1580 *)
let HOQ_QUERY1580 = slq_hist 1580 (33792, 0, [4; 9],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1581 *)
let HOQ_QUERY1581 = slq_hist 1581 (33792, 0, [6; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1582 *)
let HOQ_QUERY1582 = slq_hist 1582 (33792, 0, [8; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1583 *)
let HOQ_QUERY1583 = slq_hist 1583 (33792, 1, [0; 1],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1584 *)
let HOQ_QUERY1584 = slq_hist 1584 (33792, 1, [0; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1585 *)
let HOQ_QUERY1585 = slq_hist 1585 (33792, 1, [1; 2],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1586 *)
let HOQ_QUERY1586 = slq_hist 1586 (33792, 1, [0; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1587 *)
let HOQ_QUERY1587 = slq_hist 1587 (33792, 1, [1; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1588 *)
let HOQ_QUERY1588 = slq_hist 1588 (33792, 1, [2; 3],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1589 *)
let HOQ_QUERY1589 = slq_hist 1589 (33792, 1, [0; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1590 *)
let HOQ_QUERY1590 = slq_hist 1590 (33792, 1, [1; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1591 *)
let HOQ_QUERY1591 = slq_hist 1591 (33792, 1, [2; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1592 *)
let HOQ_QUERY1592 = slq_hist 1592 (33792, 1, [3; 4],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1593 *)
let HOQ_QUERY1593 = slq_hist 1593 (33792, 1, [0; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1594 *)
let HOQ_QUERY1594 = slq_hist 1594 (33792, 1, [1; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1595 *)
let HOQ_QUERY1595 = slq_hist 1595 (33792, 1, [2; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1596 *)
let HOQ_QUERY1596 = slq_hist 1596 (33792, 1, [3; 5],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1597 *)
let HOQ_QUERY1597 = slq_hist 1597 (33792, 1, [4; 5],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1598 *)
let HOQ_QUERY1598 = slq_hist 1598 (33792, 1, [0; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1599 *)
let HOQ_QUERY1599 = slq_hist 1599 (33792, 1, [1; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
