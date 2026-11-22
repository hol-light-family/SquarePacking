(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries051.lean                          *)
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

(* Lean: query1632 *)
let HOQ_QUERY1632 = slq_hist 1632 (33792, 2, [3; 5; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1633 *)
let HOQ_QUERY1633 = slq_hist 1633 (33792, 2, [3; 5; 13; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1634 *)
let HOQ_QUERY1634 = slq_hist 1634 (33792, 2, [3; 5; 14; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1635 *)
let HOQ_QUERY1635 = slq_hist 1635 (33792, 2, [3; 5; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1636 *)
let HOQ_QUERY1636 = slq_hist 1636 (33792, 2, [3; 5; 13; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1637 *)
let HOQ_QUERY1637 = slq_hist 1637 (33792, 2, [3; 5; 16; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1638 *)
let HOQ_QUERY1638 = slq_hist 1638 (33792, 2, [3; 5; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1639 *)
let HOQ_QUERY1639 = slq_hist 1639 (33792, 2, [3; 5; 16; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1640 *)
let HOQ_QUERY1640 = slq_hist 1640 (33792, 2, [3; 5; 17; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1641 *)
let HOQ_QUERY1641 = slq_hist 1641 (33792, 2, [4; 5; 14; 16],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1642 *)
let HOQ_QUERY1642 = slq_hist 1642 (33792, 2, [4; 5; 17],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1643 *)
let HOQ_QUERY1643 = slq_hist 1643 (33792, 2, [4; 5; 13; 17],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1644 *)
let HOQ_QUERY1644 = slq_hist 1644 (33792, 2, [4; 5; 14; 17],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1645 *)
let HOQ_QUERY1645 = slq_hist 1645 (33792, 2, [4; 5; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1646 *)
let HOQ_QUERY1646 = slq_hist 1646 (33792, 2, [4; 5; 17; 19],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1647 *)
let HOQ_QUERY1647 = slq_hist 1647 (33792, 2, [7; 16],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1648 *)
let HOQ_QUERY1648 = slq_hist 1648 (33792, 2, [7; 13; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1649 *)
let HOQ_QUERY1649 = slq_hist 1649 (33792, 2, [7; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1650 *)
let HOQ_QUERY1650 = slq_hist 1650 (33792, 2, [7; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1651 *)
let HOQ_QUERY1651 = slq_hist 1651 (33792, 2, [7; 19],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1652 *)
let HOQ_QUERY1652 = slq_hist 1652 (33792, 2, [7; 16; 19],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1653 *)
let HOQ_QUERY1653 = slq_hist 1653 (33792, 2, [3; 7; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1654 *)
let HOQ_QUERY1654 = slq_hist 1654 (33792, 2, [3; 7; 13; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1655 *)
let HOQ_QUERY1655 = slq_hist 1655 (33792, 2, [3; 7; 14; 16],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1656 *)
let HOQ_QUERY1656 = slq_hist 1656 (33792, 2, [3; 7; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1657 *)
let HOQ_QUERY1657 = slq_hist 1657 (33792, 2, [3; 7; 13; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1658 *)
let HOQ_QUERY1658 = slq_hist 1658 (33792, 2, [3; 7; 16; 17],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1659 *)
let HOQ_QUERY1659 = slq_hist 1659 (33792, 2, [3; 7; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1660 *)
let HOQ_QUERY1660 = slq_hist 1660 (33792, 2, [3; 7; 16; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1661 *)
let HOQ_QUERY1661 = slq_hist 1661 (33792, 2, [3; 7; 17; 19],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query1662 *)
let HOQ_QUERY1662 = slq_hist 1662 (33792, 2, [5; 7; 16],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1663 *)
let HOQ_QUERY1663 = slq_hist 1663 (33792, 2, [5; 7; 13; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
