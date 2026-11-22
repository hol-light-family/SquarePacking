(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries022.lean                          *)
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

(* Lean: query704 *)
let HOQ_QUERY704 = slq_hist 704 (32, 1, [0; 5; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query705 *)
let HOQ_QUERY705 = slq_hist 705 (32, 1, [1; 5; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query706 *)
let HOQ_QUERY706 = slq_hist 706 (32, 1, [2; 5; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query707 *)
let HOQ_QUERY707 = slq_hist 707 (32, 1, [3; 5; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query708 *)
let HOQ_QUERY708 = slq_hist 708 (32, 1, [4; 5; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query709 *)
let HOQ_QUERY709 = slq_hist 709 (32, 1, [6; 8],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query710 *)
let HOQ_QUERY710 = slq_hist 710 (32, 1, [0; 6; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query711 *)
let HOQ_QUERY711 = slq_hist 711 (32, 1, [1; 6; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query712 *)
let HOQ_QUERY712 = slq_hist 712 (32, 1, [2; 6; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713 *)
let HOQ_QUERY713 = slq_hist 713 (32, 1, [3; 6; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query714 *)
let HOQ_QUERY714 = slq_hist 714 (32, 1, [4; 6; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query715 *)
let HOQ_QUERY715 = slq_hist 715 (32, 1, [5; 6; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query716 *)
let HOQ_QUERY716 = slq_hist 716 (32, 1, [7; 8],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query717 *)
let HOQ_QUERY717 = slq_hist 717 (32, 1, [0; 7; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query718 *)
let HOQ_QUERY718 = slq_hist 718 (32, 1, [1; 7; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query719 *)
let HOQ_QUERY719 = slq_hist 719 (32, 1, [2; 7; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query720 *)
let HOQ_QUERY720 = slq_hist 720 (32, 1, [3; 7; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query721 *)
let HOQ_QUERY721 = slq_hist 721 (32, 1, [4; 7; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query722 *)
let HOQ_QUERY722 = slq_hist 722 (32, 1, [5; 7; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query723 *)
let HOQ_QUERY723 = slq_hist 723 (32, 1, [6; 7; 8],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query724 *)
let HOQ_QUERY724 = slq_hist 724 (32, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query725 *)
let HOQ_QUERY725 = slq_hist 725 (32, 1, [1; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query726 *)
let HOQ_QUERY726 = slq_hist 726 (32, 1, [0; 1; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query727 *)
let HOQ_QUERY727 = slq_hist 727 (32, 1, [2; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query728 *)
let HOQ_QUERY728 = slq_hist 728 (32, 1, [0; 2; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query729 *)
let HOQ_QUERY729 = slq_hist 729 (32, 1, [1; 2; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query730 *)
let HOQ_QUERY730 = slq_hist 730 (32, 1, [3; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query731 *)
let HOQ_QUERY731 = slq_hist 731 (32, 1, [0; 3; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query732 *)
let HOQ_QUERY732 = slq_hist 732 (32, 1, [1; 3; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query733 *)
let HOQ_QUERY733 = slq_hist 733 (32, 1, [2; 3; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query734 *)
let HOQ_QUERY734 = slq_hist 734 (32, 1, [4; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query735 *)
let HOQ_QUERY735 = slq_hist 735 (32, 1, [0; 4; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
