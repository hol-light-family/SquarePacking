(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries058.lean                          *)
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

(* Lean: query1856 *)
let HOQ_QUERY1856 = slq_hist 1856 (256, 2, [0; 1; 13; 15; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1857 *)
let HOQ_QUERY1857 = slq_hist 1857 (256, 2, [2; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1858 *)
let HOQ_QUERY1858 = slq_hist 1858 (256, 2, [2; 10; 12; 15],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1859 *)
let HOQ_QUERY1859 = slq_hist 1859 (256, 2, [2; 10; 13; 15],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query1860 *)
let HOQ_QUERY1860 = slq_hist 1860 (256, 2, [2; 12; 13; 15],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1861 *)
let HOQ_QUERY1861 = slq_hist 1861 (256, 2, [2; 10; 12; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1862 *)
let HOQ_QUERY1862 = slq_hist 1862 (256, 2, [2; 10; 13; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1863 *)
let HOQ_QUERY1863 = slq_hist 1863 (256, 2, [2; 12; 13; 16],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1864 *)
let HOQ_QUERY1864 = slq_hist 1864 (256, 2, [2; 12; 15; 16],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "33/20")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1865 *)
let HOQ_QUERY1865 = slq_hist 1865 (256, 2, [2; 13; 15; 16],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query1866 *)
let HOQ_QUERY1866 = slq_hist 1866 (256, 2, [0; 2; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query1867 *)
let HOQ_QUERY1867 = slq_hist 1867 (256, 2, [0; 2; 10; 12; 15],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1868 *)
let HOQ_QUERY1868 = slq_hist 1868 (256, 2, [0; 2; 10; 13; 15],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query1869 *)
let HOQ_QUERY1869 = slq_hist 1869 (256, 2, [0; 2; 12; 13; 15],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1870 *)
let HOQ_QUERY1870 = slq_hist 1870 (256, 2, [0; 2; 10; 12; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1871 *)
let HOQ_QUERY1871 = slq_hist 1871 (256, 2, [0; 2; 10; 13; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1872 *)
let HOQ_QUERY1872 = slq_hist 1872 (256, 2, [0; 2; 12; 13; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1873 *)
let HOQ_QUERY1873 = slq_hist 1873 (256, 2, [0; 2; 12; 15; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1874 *)
let HOQ_QUERY1874 = slq_hist 1874 (256, 2, [0; 2; 13; 15; 16],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query1875 *)
let HOQ_QUERY1875 = slq_hist 1875 (256, 2, [4; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1876 *)
let HOQ_QUERY1876 = slq_hist 1876 (256, 2, [0; 4; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
(* Lean: query1877 *)
let HOQ_QUERY1877 = slq_hist 1877 (256, 2, [1; 4; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1878 *)
let HOQ_QUERY1878 = slq_hist 1878 (256, 2, [1; 4; 10; 12; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1879 *)
let HOQ_QUERY1879 = slq_hist 1879 (256, 2, [1; 4; 10; 12; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1880 *)
let HOQ_QUERY1880 = slq_hist 1880 (256, 2, [1; 4; 10; 13; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1881 *)
let HOQ_QUERY1881 = slq_hist 1881 (256, 2, [1; 4; 10; 12; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1882 *)
let HOQ_QUERY1882 = slq_hist 1882 (256, 2, [1; 4; 10; 13; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1883 *)
let HOQ_QUERY1883 = slq_hist 1883 (256, 2, [1; 4; 12; 15; 16],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1884 *)
let HOQ_QUERY1884 = slq_hist 1884 (256, 2, [2; 4; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1885 *)
let HOQ_QUERY1885 = slq_hist 1885 (256, 2, [2; 4; 10; 13; 15],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query1886 *)
let HOQ_QUERY1886 = slq_hist 1886 (256, 2, [2; 4; 13; 15; 16],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query1887 *)
let HOQ_QUERY1887 = slq_hist 1887 (256, 2, [0; 5; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "113/50")]);;
