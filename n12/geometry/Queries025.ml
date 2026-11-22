(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries025.lean                          *)
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

(* Lean: query800 *)
let HOQ_QUERY800 = slq_hist 800 (192, 1, [5; 7],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query801 *)
let HOQ_QUERY801 = slq_hist 801 (192, 1, [6; 7],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query802 *)
let HOQ_QUERY802 = slq_hist 802 (192, 1, [8],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query803 *)
let HOQ_QUERY803 = slq_hist 803 (192, 1, [0; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query804 *)
let HOQ_QUERY804 = slq_hist 804 (192, 1, [1; 8],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query805 *)
let HOQ_QUERY805 = slq_hist 805 (192, 1, [2; 8],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query806 *)
let HOQ_QUERY806 = slq_hist 806 (192, 1, [3; 8],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query807 *)
let HOQ_QUERY807 = slq_hist 807 (192, 1, [4; 8],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query808 *)
let HOQ_QUERY808 = slq_hist 808 (192, 1, [5; 8],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query809 *)
let HOQ_QUERY809 = slq_hist 809 (192, 1, [6; 8],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query810 *)
let HOQ_QUERY810 = slq_hist 810 (192, 1, [7; 8],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query811 *)
let HOQ_QUERY811 = slq_hist 811 (192, 1, [9],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query812 *)
let HOQ_QUERY812 = slq_hist 812 (192, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query813 *)
let HOQ_QUERY813 = slq_hist 813 (192, 1, [1; 9],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query814 *)
let HOQ_QUERY814 = slq_hist 814 (192, 1, [2; 9],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query815 *)
let HOQ_QUERY815 = slq_hist 815 (192, 1, [3; 9],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query816 *)
let HOQ_QUERY816 = slq_hist 816 (192, 1, [4; 9],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query817 *)
let HOQ_QUERY817 = slq_hist 817 (192, 1, [5; 9],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query818 *)
let HOQ_QUERY818 = slq_hist 818 (192, 1, [6; 9],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query819 *)
let HOQ_QUERY819 = slq_hist 819 (192, 1, [7; 9],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "3")]);;
(* Lean: query820 *)
let HOQ_QUERY820 = slq_hist 820 (192, 1, [8; 9],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query821 *)
let HOQ_QUERY821 = slq_hist 821 (192, 2, [14],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "8/5", nlin_rat "3")]);;
(* Lean: query822 *)
let HOQ_QUERY822 = slq_hist 822 (192, 2, [11; 14],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "8/5", nlin_rat "3")]);;
(* Lean: query823 *)
let HOQ_QUERY823 = slq_hist 823 (768, 1, [1],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query824 *)
let HOQ_QUERY824 = slq_hist 824 (768, 1, [0; 1],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query825 *)
let HOQ_QUERY825 = slq_hist 825 (768, 1, [1; 2],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query826 *)
let HOQ_QUERY826 = slq_hist 826 (768, 1, [1; 3],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query827 *)
let HOQ_QUERY827 = slq_hist 827 (768, 1, [4],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query828 *)
let HOQ_QUERY828 = slq_hist 828 (768, 1, [0; 4],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query829 *)
let HOQ_QUERY829 = slq_hist 829 (768, 1, [1; 4],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query830 *)
let HOQ_QUERY830 = slq_hist 830 (768, 1, [2; 4],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query831 *)
let HOQ_QUERY831 = slq_hist 831 (768, 1, [3; 4],
  [(nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);;
