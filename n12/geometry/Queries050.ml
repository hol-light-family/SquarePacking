(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries050.lean                          *)
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

(* Lean: query1600 *)
let HOQ_QUERY1600 = slq_hist 1600 (33792, 1, [2; 6],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1601 *)
let HOQ_QUERY1601 = slq_hist 1601 (33792, 1, [5; 6],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1602 *)
let HOQ_QUERY1602 = slq_hist 1602 (33792, 1, [0; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1603 *)
let HOQ_QUERY1603 = slq_hist 1603 (33792, 1, [1; 7],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1604 *)
let HOQ_QUERY1604 = slq_hist 1604 (33792, 1, [2; 7],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1605 *)
let HOQ_QUERY1605 = slq_hist 1605 (33792, 1, [5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1606 *)
let HOQ_QUERY1606 = slq_hist 1606 (33792, 1, [0; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1607 *)
let HOQ_QUERY1607 = slq_hist 1607 (33792, 1, [1; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1608 *)
let HOQ_QUERY1608 = slq_hist 1608 (33792, 1, [2; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1609 *)
let HOQ_QUERY1609 = slq_hist 1609 (33792, 1, [3; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1610 *)
let HOQ_QUERY1610 = slq_hist 1610 (33792, 1, [4; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1611 *)
let HOQ_QUERY1611 = slq_hist 1611 (33792, 1, [5; 8],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1612 *)
let HOQ_QUERY1612 = slq_hist 1612 (33792, 1, [6; 8],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1613 *)
let HOQ_QUERY1613 = slq_hist 1613 (33792, 1, [7; 8],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1614 *)
let HOQ_QUERY1614 = slq_hist 1614 (33792, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1615 *)
let HOQ_QUERY1615 = slq_hist 1615 (33792, 1, [1; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1616 *)
let HOQ_QUERY1616 = slq_hist 1616 (33792, 1, [2; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1617 *)
let HOQ_QUERY1617 = slq_hist 1617 (33792, 1, [3; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1618 *)
let HOQ_QUERY1618 = slq_hist 1618 (33792, 1, [4; 9],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1619 *)
let HOQ_QUERY1619 = slq_hist 1619 (33792, 1, [5; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1620 *)
let HOQ_QUERY1620 = slq_hist 1620 (33792, 1, [8; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1621 *)
let HOQ_QUERY1621 = slq_hist 1621 (33792, 2, [3; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1622 *)
let HOQ_QUERY1622 = slq_hist 1622 (33792, 2, [3; 13; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1623 *)
let HOQ_QUERY1623 = slq_hist 1623 (33792, 2, [3; 14; 16],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1624 *)
let HOQ_QUERY1624 = slq_hist 1624 (33792, 2, [3; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1625 *)
let HOQ_QUERY1625 = slq_hist 1625 (33792, 2, [3; 13; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1626 *)
let HOQ_QUERY1626 = slq_hist 1626 (33792, 2, [3; 16; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1627 *)
let HOQ_QUERY1627 = slq_hist 1627 (33792, 2, [3; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1628 *)
let HOQ_QUERY1628 = slq_hist 1628 (33792, 2, [3; 16; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1629 *)
let HOQ_QUERY1629 = slq_hist 1629 (33792, 2, [3; 17; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1630 *)
let HOQ_QUERY1630 = slq_hist 1630 (33792, 2, [5; 14; 16],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1631 *)
let HOQ_QUERY1631 = slq_hist 1631 (33792, 2, [5; 14; 17],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
