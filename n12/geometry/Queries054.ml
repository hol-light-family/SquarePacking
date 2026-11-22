(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries054.lean                          *)
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

(* Lean: query1728 *)
let HOQ_QUERY1728 = slq_hist 1728 (48, 2, [9; 17; 19],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
(* Lean: query1729 *)
let HOQ_QUERY1729 = slq_hist 1729 (192, 2, [1; 11; 14],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "8/5", nlin_rat "3")]);;
(* Lean: query1730 *)
let HOQ_QUERY1730 = slq_hist 1730 (256, 1, [0; 1; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1731 *)
let HOQ_QUERY1731 = slq_hist 1731 (256, 1, [1; 2; 3],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1732 *)
let HOQ_QUERY1732 = slq_hist 1732 (256, 1, [0; 1; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1733 *)
let HOQ_QUERY1733 = slq_hist 1733 (256, 1, [0; 2; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1734 *)
let HOQ_QUERY1734 = slq_hist 1734 (256, 1, [1; 2; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1735 *)
let HOQ_QUERY1735 = slq_hist 1735 (256, 1, [0; 3; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1736 *)
let HOQ_QUERY1736 = slq_hist 1736 (256, 1, [1; 3; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1737 *)
let HOQ_QUERY1737 = slq_hist 1737 (256, 1, [2; 3; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1738 *)
let HOQ_QUERY1738 = slq_hist 1738 (256, 1, [0; 1; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1739 *)
let HOQ_QUERY1739 = slq_hist 1739 (256, 1, [1; 2; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1740 *)
let HOQ_QUERY1740 = slq_hist 1740 (256, 1, [1; 3; 5],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1741 *)
let HOQ_QUERY1741 = slq_hist 1741 (256, 1, [0; 4; 5],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1742 *)
let HOQ_QUERY1742 = slq_hist 1742 (256, 1, [1; 4; 5],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1743 *)
let HOQ_QUERY1743 = slq_hist 1743 (256, 1, [2; 4; 5],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1744 *)
let HOQ_QUERY1744 = slq_hist 1744 (256, 1, [3; 4; 5],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1745 *)
let HOQ_QUERY1745 = slq_hist 1745 (256, 1, [0; 1; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1746 *)
let HOQ_QUERY1746 = slq_hist 1746 (256, 1, [1; 2; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1747 *)
let HOQ_QUERY1747 = slq_hist 1747 (256, 1, [1; 3; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1748 *)
let HOQ_QUERY1748 = slq_hist 1748 (256, 1, [0; 4; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1749 *)
let HOQ_QUERY1749 = slq_hist 1749 (256, 1, [1; 4; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1750 *)
let HOQ_QUERY1750 = slq_hist 1750 (256, 1, [2; 4; 6],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1751 *)
let HOQ_QUERY1751 = slq_hist 1751 (256, 1, [3; 4; 6],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1752 *)
let HOQ_QUERY1752 = slq_hist 1752 (256, 1, [0; 5; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1753 *)
let HOQ_QUERY1753 = slq_hist 1753 (256, 1, [1; 5; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1754 *)
let HOQ_QUERY1754 = slq_hist 1754 (256, 1, [4; 5; 6],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1755 *)
let HOQ_QUERY1755 = slq_hist 1755 (256, 1, [0; 1; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1756 *)
let HOQ_QUERY1756 = slq_hist 1756 (256, 1, [0; 2; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1757 *)
let HOQ_QUERY1757 = slq_hist 1757 (256, 1, [1; 2; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1758 *)
let HOQ_QUERY1758 = slq_hist 1758 (256, 1, [0; 3; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1759 *)
let HOQ_QUERY1759 = slq_hist 1759 (256, 1, [1; 3; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
