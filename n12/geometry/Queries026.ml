(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries026.lean                          *)
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

(* Lean: query832 *)
let HOQ_QUERY832 = slq_hist 832 (768, 1, [1; 5],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query833 *)
let HOQ_QUERY833 = slq_hist 833 (768, 1, [4; 5],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query834 *)
let HOQ_QUERY834 = slq_hist 834 (768, 1, [1; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query835 *)
let HOQ_QUERY835 = slq_hist 835 (768, 1, [4; 6],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query836 *)
let HOQ_QUERY836 = slq_hist 836 (768, 1, [7],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query837 *)
let HOQ_QUERY837 = slq_hist 837 (768, 1, [0; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query838 *)
let HOQ_QUERY838 = slq_hist 838 (768, 1, [1; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query839 *)
let HOQ_QUERY839 = slq_hist 839 (768, 1, [2; 7],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query840 *)
let HOQ_QUERY840 = slq_hist 840 (768, 1, [3; 7],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query841 *)
let HOQ_QUERY841 = slq_hist 841 (768, 1, [4; 7],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query842 *)
let HOQ_QUERY842 = slq_hist 842 (768, 1, [5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query843 *)
let HOQ_QUERY843 = slq_hist 843 (768, 1, [6; 7],
  [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query844 *)
let HOQ_QUERY844 = slq_hist 844 (768, 1, [1; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query845 *)
let HOQ_QUERY845 = slq_hist 845 (768, 1, [4; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query846 *)
let HOQ_QUERY846 = slq_hist 846 (768, 1, [7; 8],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query847 *)
let HOQ_QUERY847 = slq_hist 847 (768, 1, [9],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query848 *)
let HOQ_QUERY848 = slq_hist 848 (768, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query849 *)
let HOQ_QUERY849 = slq_hist 849 (768, 1, [1; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query850 *)
let HOQ_QUERY850 = slq_hist 850 (768, 1, [2; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query851 *)
let HOQ_QUERY851 = slq_hist 851 (768, 1, [3; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query852 *)
let HOQ_QUERY852 = slq_hist 852 (768, 1, [4; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query853 *)
let HOQ_QUERY853 = slq_hist 853 (768, 1, [5; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query854 *)
let HOQ_QUERY854 = slq_hist 854 (768, 1, [6; 9],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query855 *)
let HOQ_QUERY855 = slq_hist 855 (768, 1, [7; 9],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query856 *)
let HOQ_QUERY856 = slq_hist 856 (768, 1, [8; 9],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query857 *)
let HOQ_QUERY857 = slq_hist 857 (3072, 0, [0],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query858 *)
let HOQ_QUERY858 = slq_hist 858 (3072, 0, [1],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query859 *)
let HOQ_QUERY859 = slq_hist 859 (3072, 0, [2],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query860 *)
let HOQ_QUERY860 = slq_hist 860 (3072, 0, [3],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query861 *)
let HOQ_QUERY861 = slq_hist 861 (3072, 0, [4],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query862 *)
let HOQ_QUERY862 = slq_hist 862 (3072, 0, [6],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query863 *)
let HOQ_QUERY863 = slq_hist 863 (3072, 0, [7],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);;
