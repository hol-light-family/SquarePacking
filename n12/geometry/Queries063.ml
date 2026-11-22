(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries063.lean                          *)
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

(* Lean: query2016 *)
let HOQ_QUERY2016 = slq_hist 2016 (512, 1, [3; 8; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2017 *)
let HOQ_QUERY2017 = slq_hist 2017 (512, 1, [4; 8; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2018 *)
let HOQ_QUERY2018 = slq_hist 2018 (512, 1, [5; 8; 9],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2019 *)
let HOQ_QUERY2019 = slq_hist 2019 (512, 1, [7; 8; 9],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query2020 *)
let HOQ_QUERY2020 = slq_hist 2020 (512, 2, [4; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query2021 *)
let HOQ_QUERY2021 = slq_hist 2021 (512, 2, [2; 4; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2022 *)
let HOQ_QUERY2022 = slq_hist 2022 (512, 2, [2; 4; 12; 13; 16],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2023 *)
let HOQ_QUERY2023 = slq_hist 2023 (512, 2, [2; 4; 12; 15; 16],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2024 *)
let HOQ_QUERY2024 = slq_hist 2024 (512, 2, [2; 4; 13; 15; 16],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query2025 *)
let HOQ_QUERY2025 = slq_hist 2025 (512, 2, [2; 4; 12; 15; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2026 *)
let HOQ_QUERY2026 = slq_hist 2026 (512, 2, [2; 4; 13; 15; 18],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query2027 *)
let HOQ_QUERY2027 = slq_hist 2027 (512, 2, [2; 4; 12; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2028 *)
let HOQ_QUERY2028 = slq_hist 2028 (512, 2, [2; 4; 13; 16; 18],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2029 *)
let HOQ_QUERY2029 = slq_hist 2029 (512, 2, [2; 4; 15; 16; 18],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query2030 *)
let HOQ_QUERY2030 = slq_hist 2030 (512, 2, [2; 4; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query2031 *)
let HOQ_QUERY2031 = slq_hist 2031 (512, 2, [4; 5; 12; 13; 15],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2032 *)
let HOQ_QUERY2032 = slq_hist 2032 (512, 2, [4; 5; 12; 15; 18],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2033 *)
let HOQ_QUERY2033 = slq_hist 2033 (512, 2, [4; 5; 13; 15; 18],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2034 *)
let HOQ_QUERY2034 = slq_hist 2034 (512, 2, [4; 5; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query2035 *)
let HOQ_QUERY2035 = slq_hist 2035 (512, 2, [6; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2036 *)
let HOQ_QUERY2036 = slq_hist 2036 (512, 2, [6; 12; 13; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2037 *)
let HOQ_QUERY2037 = slq_hist 2037 (512, 2, [6; 12; 15; 16],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2038 *)
let HOQ_QUERY2038 = slq_hist 2038 (512, 2, [6; 13; 15; 16],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2039 *)
let HOQ_QUERY2039 = slq_hist 2039 (512, 2, [6; 12; 15; 18],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2040 *)
let HOQ_QUERY2040 = slq_hist 2040 (512, 2, [6; 13; 15; 18],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2041 *)
let HOQ_QUERY2041 = slq_hist 2041 (512, 2, [6; 12; 16; 18],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query2042 *)
let HOQ_QUERY2042 = slq_hist 2042 (512, 2, [6; 13; 16; 18],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query2043 *)
let HOQ_QUERY2043 = slq_hist 2043 (512, 2, [6; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query2044 *)
let HOQ_QUERY2044 = slq_hist 2044 (512, 2, [4; 6; 12; 13; 16],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query2045 *)
let HOQ_QUERY2045 = slq_hist 2045 (512, 2, [4; 6; 12; 16; 18],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1")]);;
(* Lean: query2046 *)
let HOQ_QUERY2046 = slq_hist 2046 (512, 2, [4; 6; 16; 18; 19],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query2047 *)
let HOQ_QUERY2047 = slq_hist 2047 (512, 2, [8; 12; 13; 15],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
