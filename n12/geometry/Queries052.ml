(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries052.lean                          *)
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

(* Lean: query1664 *)
let HOQ_QUERY1664 = slq_hist 1664 (33792, 2, [5; 7; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1665 *)
let HOQ_QUERY1665 = slq_hist 1665 (33792, 2, [5; 7; 19],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1666 *)
let HOQ_QUERY1666 = slq_hist 1666 (33792, 2, [5; 7; 16; 19],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1667 *)
let HOQ_QUERY1667 = slq_hist 1667 (33792, 2, [5; 8; 14; 16],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1668 *)
let HOQ_QUERY1668 = slq_hist 1668 (33792, 2, [5; 8; 17],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1669 *)
let HOQ_QUERY1669 = slq_hist 1669 (33792, 2, [5; 8; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1670 *)
let HOQ_QUERY1670 = slq_hist 1670 (33792, 2, [5; 8; 14; 17],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1671 *)
let HOQ_QUERY1671 = slq_hist 1671 (33792, 2, [5; 8; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query1672 *)
let HOQ_QUERY1672 = slq_hist 1672 (33792, 2, [5; 8; 16; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query1673 *)
let HOQ_QUERY1673 = slq_hist 1673 (33792, 2, [5; 8; 17; 19],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query1674 *)
let HOQ_QUERY1674 = slq_hist 1674 (33792, 2, [5; 9; 14; 16],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1675 *)
let HOQ_QUERY1675 = slq_hist 1675 (33792, 2, [5; 9; 14; 17],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1676 *)
let HOQ_QUERY1676 = slq_hist 1676 (33792, 2, [7; 9; 16],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1677 *)
let HOQ_QUERY1677 = slq_hist 1677 (33792, 2, [7; 9; 13; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1678 *)
let HOQ_QUERY1678 = slq_hist 1678 (33792, 2, [7; 9; 14; 16],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1679 *)
let HOQ_QUERY1679 = slq_hist 1679 (33792, 2, [7; 9; 13; 17],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query1680 *)
let HOQ_QUERY1680 = slq_hist 1680 (33792, 2, [7; 9; 19],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1681 *)
let HOQ_QUERY1681 = slq_hist 1681 (33792, 2, [7; 9; 16; 19],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1682 *)
let HOQ_QUERY1682 = slq_hist 1682 (12, 2, [8; 15; 18],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]);;
(* Lean: query1683 *)
let HOQ_QUERY1683 = slq_hist 1683 (48, 1, [0; 1],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1684 *)
let HOQ_QUERY1684 = slq_hist 1684 (48, 1, [0; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1685 *)
let HOQ_QUERY1685 = slq_hist 1685 (48, 1, [1; 2],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1686 *)
let HOQ_QUERY1686 = slq_hist 1686 (48, 1, [0; 3],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1687 *)
let HOQ_QUERY1687 = slq_hist 1687 (48, 1, [1; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1688 *)
let HOQ_QUERY1688 = slq_hist 1688 (48, 1, [2; 3],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1689 *)
let HOQ_QUERY1689 = slq_hist 1689 (48, 1, [0; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1690 *)
let HOQ_QUERY1690 = slq_hist 1690 (48, 1, [1; 4],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1691 *)
let HOQ_QUERY1691 = slq_hist 1691 (48, 1, [2; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1692 *)
let HOQ_QUERY1692 = slq_hist 1692 (48, 1, [3; 4],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1693 *)
let HOQ_QUERY1693 = slq_hist 1693 (48, 1, [0; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1694 *)
let HOQ_QUERY1694 = slq_hist 1694 (48, 1, [1; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1695 *)
let HOQ_QUERY1695 = slq_hist 1695 (48, 1, [2; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
