(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries059.lean                          *)
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

(* Lean: query1888 *)
let HOQ_QUERY1888 = slq_hist 1888 (256, 2, [0; 5; 10; 12; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1889 *)
let HOQ_QUERY1889 = slq_hist 1889 (256, 2, [0; 5; 10; 13; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1890 *)
let HOQ_QUERY1890 = slq_hist 1890 (256, 2, [0; 5; 12; 13; 15],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1891 *)
let HOQ_QUERY1891 = slq_hist 1891 (256, 2, [0; 5; 10; 12; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1892 *)
let HOQ_QUERY1892 = slq_hist 1892 (256, 2, [0; 5; 10; 13; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1893 *)
let HOQ_QUERY1893 = slq_hist 1893 (256, 2, [0; 5; 12; 13; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1894 *)
let HOQ_QUERY1894 = slq_hist 1894 (256, 2, [0; 5; 12; 15; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1895 *)
let HOQ_QUERY1895 = slq_hist 1895 (256, 2, [0; 5; 13; 15; 16],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query1896 *)
let HOQ_QUERY1896 = slq_hist 1896 (256, 2, [4; 5; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1897 *)
let HOQ_QUERY1897 = slq_hist 1897 (256, 2, [4; 5; 10; 12; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1898 *)
let HOQ_QUERY1898 = slq_hist 1898 (256, 2, [4; 5; 10; 12; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1899 *)
let HOQ_QUERY1899 = slq_hist 1899 (256, 2, [4; 5; 12; 15; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1900 *)
let HOQ_QUERY1900 = slq_hist 1900 (256, 2, [4; 6; 10; 11; 13],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "87/50")]);;
(* Lean: query1901 *)
let HOQ_QUERY1901 = slq_hist 1901 (256, 2, [4; 6; 10; 12; 13],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query1902 *)
let HOQ_QUERY1902 = slq_hist 1902 (256, 2, [4; 6; 10; 12; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1903 *)
let HOQ_QUERY1903 = slq_hist 1903 (256, 2, [4; 6; 10; 13; 15],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1904 *)
let HOQ_QUERY1904 = slq_hist 1904 (256, 2, [4; 6; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1905 *)
let HOQ_QUERY1905 = slq_hist 1905 (256, 2, [4; 6; 10; 12; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query1906 *)
let HOQ_QUERY1906 = slq_hist 1906 (256, 2, [4; 6; 10; 13; 16],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1907 *)
let HOQ_QUERY1907 = slq_hist 1907 (256, 2, [4; 6; 12; 13; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query1908 *)
let HOQ_QUERY1908 = slq_hist 1908 (256, 2, [4; 6; 12; 15; 16],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1909 *)
let HOQ_QUERY1909 = slq_hist 1909 (256, 2, [4; 6; 13; 15; 16],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1910 *)
let HOQ_QUERY1910 = slq_hist 1910 (512, 1, [0; 1; 2],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1911 *)
let HOQ_QUERY1911 = slq_hist 1911 (512, 1, [0; 1; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1912 *)
let HOQ_QUERY1912 = slq_hist 1912 (512, 1, [0; 2; 3],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1913 *)
let HOQ_QUERY1913 = slq_hist 1913 (512, 1, [1; 2; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1914 *)
let HOQ_QUERY1914 = slq_hist 1914 (512, 1, [0; 1; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1915 *)
let HOQ_QUERY1915 = slq_hist 1915 (512, 1, [0; 2; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1916 *)
let HOQ_QUERY1916 = slq_hist 1916 (512, 1, [1; 2; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1917 *)
let HOQ_QUERY1917 = slq_hist 1917 (512, 1, [0; 3; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1918 *)
let HOQ_QUERY1918 = slq_hist 1918 (512, 1, [1; 3; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1919 *)
let HOQ_QUERY1919 = slq_hist 1919 (512, 1, [2; 3; 4],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2")]);;
