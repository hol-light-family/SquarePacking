(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries056.lean                          *)
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

(* Lean: query1792 *)
let HOQ_QUERY1792 = slq_hist 1792 (256, 1, [1; 6; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1793 *)
let HOQ_QUERY1793 = slq_hist 1793 (256, 1, [2; 6; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1794 *)
let HOQ_QUERY1794 = slq_hist 1794 (256, 1, [3; 6; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1795 *)
let HOQ_QUERY1795 = slq_hist 1795 (256, 1, [4; 6; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1796 *)
let HOQ_QUERY1796 = slq_hist 1796 (256, 1, [5; 6; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1797 *)
let HOQ_QUERY1797 = slq_hist 1797 (256, 1, [0; 7; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1798 *)
let HOQ_QUERY1798 = slq_hist 1798 (256, 1, [1; 7; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1799 *)
let HOQ_QUERY1799 = slq_hist 1799 (256, 1, [2; 7; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1800 *)
let HOQ_QUERY1800 = slq_hist 1800 (256, 1, [3; 7; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1801 *)
let HOQ_QUERY1801 = slq_hist 1801 (256, 1, [4; 7; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1802 *)
let HOQ_QUERY1802 = slq_hist 1802 (256, 1, [5; 7; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1803 *)
let HOQ_QUERY1803 = slq_hist 1803 (256, 1, [6; 7; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1804 *)
let HOQ_QUERY1804 = slq_hist 1804 (256, 1, [0; 1; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1805 *)
let HOQ_QUERY1805 = slq_hist 1805 (256, 1, [0; 2; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1806 *)
let HOQ_QUERY1806 = slq_hist 1806 (256, 1, [1; 2; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1807 *)
let HOQ_QUERY1807 = slq_hist 1807 (256, 1, [0; 3; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1808 *)
let HOQ_QUERY1808 = slq_hist 1808 (256, 1, [1; 3; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1809 *)
let HOQ_QUERY1809 = slq_hist 1809 (256, 1, [2; 3; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1810 *)
let HOQ_QUERY1810 = slq_hist 1810 (256, 1, [0; 4; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1811 *)
let HOQ_QUERY1811 = slq_hist 1811 (256, 1, [1; 4; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1812 *)
let HOQ_QUERY1812 = slq_hist 1812 (256, 1, [2; 4; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1813 *)
let HOQ_QUERY1813 = slq_hist 1813 (256, 1, [3; 4; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1814 *)
let HOQ_QUERY1814 = slq_hist 1814 (256, 1, [0; 5; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1815 *)
let HOQ_QUERY1815 = slq_hist 1815 (256, 1, [1; 5; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1816 *)
let HOQ_QUERY1816 = slq_hist 1816 (256, 1, [2; 5; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1817 *)
let HOQ_QUERY1817 = slq_hist 1817 (256, 1, [3; 5; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1818 *)
let HOQ_QUERY1818 = slq_hist 1818 (256, 1, [4; 5; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1819 *)
let HOQ_QUERY1819 = slq_hist 1819 (256, 1, [0; 6; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1820 *)
let HOQ_QUERY1820 = slq_hist 1820 (256, 1, [1; 6; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1821 *)
let HOQ_QUERY1821 = slq_hist 1821 (256, 1, [2; 6; 9],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1822 *)
let HOQ_QUERY1822 = slq_hist 1822 (256, 1, [3; 6; 9],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1823 *)
let HOQ_QUERY1823 = slq_hist 1823 (256, 1, [4; 6; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
