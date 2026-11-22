(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries055.lean                          *)
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

(* Lean: query1760 *)
let HOQ_QUERY1760 = slq_hist 1760 (256, 1, [2; 3; 7],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1761 *)
let HOQ_QUERY1761 = slq_hist 1761 (256, 1, [0; 4; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1762 *)
let HOQ_QUERY1762 = slq_hist 1762 (256, 1, [1; 4; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1763 *)
let HOQ_QUERY1763 = slq_hist 1763 (256, 1, [2; 4; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1764 *)
let HOQ_QUERY1764 = slq_hist 1764 (256, 1, [3; 4; 7],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1765 *)
let HOQ_QUERY1765 = slq_hist 1765 (256, 1, [0; 5; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1766 *)
let HOQ_QUERY1766 = slq_hist 1766 (256, 1, [1; 5; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1767 *)
let HOQ_QUERY1767 = slq_hist 1767 (256, 1, [2; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1768 *)
let HOQ_QUERY1768 = slq_hist 1768 (256, 1, [3; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1769 *)
let HOQ_QUERY1769 = slq_hist 1769 (256, 1, [4; 5; 7],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1770 *)
let HOQ_QUERY1770 = slq_hist 1770 (256, 1, [0; 6; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1771 *)
let HOQ_QUERY1771 = slq_hist 1771 (256, 1, [1; 6; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1772 *)
let HOQ_QUERY1772 = slq_hist 1772 (256, 1, [2; 6; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1773 *)
let HOQ_QUERY1773 = slq_hist 1773 (256, 1, [3; 6; 7],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1774 *)
let HOQ_QUERY1774 = slq_hist 1774 (256, 1, [4; 6; 7],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1775 *)
let HOQ_QUERY1775 = slq_hist 1775 (256, 1, [5; 6; 7],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1776 *)
let HOQ_QUERY1776 = slq_hist 1776 (256, 1, [0; 1; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1777 *)
let HOQ_QUERY1777 = slq_hist 1777 (256, 1, [0; 2; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1778 *)
let HOQ_QUERY1778 = slq_hist 1778 (256, 1, [1; 2; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1779 *)
let HOQ_QUERY1779 = slq_hist 1779 (256, 1, [0; 3; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1780 *)
let HOQ_QUERY1780 = slq_hist 1780 (256, 1, [1; 3; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1781 *)
let HOQ_QUERY1781 = slq_hist 1781 (256, 1, [2; 3; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1782 *)
let HOQ_QUERY1782 = slq_hist 1782 (256, 1, [0; 4; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1783 *)
let HOQ_QUERY1783 = slq_hist 1783 (256, 1, [1; 4; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1784 *)
let HOQ_QUERY1784 = slq_hist 1784 (256, 1, [2; 4; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1785 *)
let HOQ_QUERY1785 = slq_hist 1785 (256, 1, [3; 4; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1786 *)
let HOQ_QUERY1786 = slq_hist 1786 (256, 1, [0; 5; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1787 *)
let HOQ_QUERY1787 = slq_hist 1787 (256, 1, [1; 5; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1788 *)
let HOQ_QUERY1788 = slq_hist 1788 (256, 1, [2; 5; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1789 *)
let HOQ_QUERY1789 = slq_hist 1789 (256, 1, [3; 5; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1790 *)
let HOQ_QUERY1790 = slq_hist 1790 (256, 1, [4; 5; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1791 *)
let HOQ_QUERY1791 = slq_hist 1791 (256, 1, [0; 6; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
