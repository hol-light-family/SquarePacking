(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries057.lean                          *)
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

(* Lean: query1824 *)
let HOQ_QUERY1824 = slq_hist 1824 (256, 1, [5; 6; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1825 *)
let HOQ_QUERY1825 = slq_hist 1825 (256, 1, [0; 7; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1826 *)
let HOQ_QUERY1826 = slq_hist 1826 (256, 1, [1; 7; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1827 *)
let HOQ_QUERY1827 = slq_hist 1827 (256, 1, [2; 7; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1828 *)
let HOQ_QUERY1828 = slq_hist 1828 (256, 1, [3; 7; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1829 *)
let HOQ_QUERY1829 = slq_hist 1829 (256, 1, [4; 7; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1830 *)
let HOQ_QUERY1830 = slq_hist 1830 (256, 1, [5; 7; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1831 *)
let HOQ_QUERY1831 = slq_hist 1831 (256, 1, [6; 7; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1832 *)
let HOQ_QUERY1832 = slq_hist 1832 (256, 1, [0; 8; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1833 *)
let HOQ_QUERY1833 = slq_hist 1833 (256, 1, [1; 8; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1834 *)
let HOQ_QUERY1834 = slq_hist 1834 (256, 1, [2; 8; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1835 *)
let HOQ_QUERY1835 = slq_hist 1835 (256, 1, [3; 8; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1836 *)
let HOQ_QUERY1836 = slq_hist 1836 (256, 1, [4; 8; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1837 *)
let HOQ_QUERY1837 = slq_hist 1837 (256, 1, [5; 8; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1838 *)
let HOQ_QUERY1838 = slq_hist 1838 (256, 1, [6; 8; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1839 *)
let HOQ_QUERY1839 = slq_hist 1839 (256, 1, [7; 8; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1840 *)
let HOQ_QUERY1840 = slq_hist 1840 (256, 2, [0; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query1841 *)
let HOQ_QUERY1841 = slq_hist 1841 (256, 2, [0; 10; 12; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1842 *)
let HOQ_QUERY1842 = slq_hist 1842 (256, 2, [0; 10; 13; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1843 *)
let HOQ_QUERY1843 = slq_hist 1843 (256, 2, [0; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1844 *)
let HOQ_QUERY1844 = slq_hist 1844 (256, 2, [0; 10; 12; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1845 *)
let HOQ_QUERY1845 = slq_hist 1845 (256, 2, [0; 10; 13; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1846 *)
let HOQ_QUERY1846 = slq_hist 1846 (256, 2, [0; 12; 13; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1847 *)
let HOQ_QUERY1847 = slq_hist 1847 (256, 2, [0; 12; 15; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1848 *)
let HOQ_QUERY1848 = slq_hist 1848 (256, 2, [0; 13; 15; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1849 *)
let HOQ_QUERY1849 = slq_hist 1849 (256, 2, [0; 1; 10; 12; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1850 *)
let HOQ_QUERY1850 = slq_hist 1850 (256, 2, [0; 1; 10; 13; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1851 *)
let HOQ_QUERY1851 = slq_hist 1851 (256, 2, [0; 1; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1852 *)
let HOQ_QUERY1852 = slq_hist 1852 (256, 2, [0; 1; 10; 12; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1853 *)
let HOQ_QUERY1853 = slq_hist 1853 (256, 2, [0; 1; 10; 13; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1854 *)
let HOQ_QUERY1854 = slq_hist 1854 (256, 2, [0; 1; 12; 13; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1855 *)
let HOQ_QUERY1855 = slq_hist 1855 (256, 2, [0; 1; 12; 15; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
