(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries061.lean                          *)
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

(* Lean: query1952 *)
let HOQ_QUERY1952 = slq_hist 1952 (512, 1, [1; 5; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1953 *)
let HOQ_QUERY1953 = slq_hist 1953 (512, 1, [2; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1954 *)
let HOQ_QUERY1954 = slq_hist 1954 (512, 1, [3; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1955 *)
let HOQ_QUERY1955 = slq_hist 1955 (512, 1, [4; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1956 *)
let HOQ_QUERY1956 = slq_hist 1956 (512, 1, [0; 6; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1957 *)
let HOQ_QUERY1957 = slq_hist 1957 (512, 1, [1; 6; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1958 *)
let HOQ_QUERY1958 = slq_hist 1958 (512, 1, [2; 6; 7],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1959 *)
let HOQ_QUERY1959 = slq_hist 1959 (512, 1, [3; 6; 7],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1960 *)
let HOQ_QUERY1960 = slq_hist 1960 (512, 1, [4; 6; 7],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1961 *)
let HOQ_QUERY1961 = slq_hist 1961 (512, 1, [5; 6; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1962 *)
let HOQ_QUERY1962 = slq_hist 1962 (512, 1, [0; 1; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1963 *)
let HOQ_QUERY1963 = slq_hist 1963 (512, 1, [0; 2; 8],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1964 *)
let HOQ_QUERY1964 = slq_hist 1964 (512, 1, [1; 2; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1965 *)
let HOQ_QUERY1965 = slq_hist 1965 (512, 1, [0; 3; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1966 *)
let HOQ_QUERY1966 = slq_hist 1966 (512, 1, [1; 3; 8],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1967 *)
let HOQ_QUERY1967 = slq_hist 1967 (512, 1, [2; 3; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1968 *)
let HOQ_QUERY1968 = slq_hist 1968 (512, 1, [0; 4; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1969 *)
let HOQ_QUERY1969 = slq_hist 1969 (512, 1, [1; 4; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1970 *)
let HOQ_QUERY1970 = slq_hist 1970 (512, 1, [2; 4; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1971 *)
let HOQ_QUERY1971 = slq_hist 1971 (512, 1, [3; 4; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1972 *)
let HOQ_QUERY1972 = slq_hist 1972 (512, 1, [0; 5; 8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1973 *)
let HOQ_QUERY1973 = slq_hist 1973 (512, 1, [1; 5; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1974 *)
let HOQ_QUERY1974 = slq_hist 1974 (512, 1, [4; 5; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1975 *)
let HOQ_QUERY1975 = slq_hist 1975 (512, 1, [0; 6; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1976 *)
let HOQ_QUERY1976 = slq_hist 1976 (512, 1, [1; 6; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1977 *)
let HOQ_QUERY1977 = slq_hist 1977 (512, 1, [4; 6; 8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1978 *)
let HOQ_QUERY1978 = slq_hist 1978 (512, 1, [0; 7; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1979 *)
let HOQ_QUERY1979 = slq_hist 1979 (512, 1, [1; 7; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1980 *)
let HOQ_QUERY1980 = slq_hist 1980 (512, 1, [2; 7; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1981 *)
let HOQ_QUERY1981 = slq_hist 1981 (512, 1, [3; 7; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1982 *)
let HOQ_QUERY1982 = slq_hist 1982 (512, 1, [4; 7; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1983 *)
let HOQ_QUERY1983 = slq_hist 1983 (512, 1, [5; 7; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
