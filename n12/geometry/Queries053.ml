(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries053.lean                          *)
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

(* Lean: query1696 *)
let HOQ_QUERY1696 = slq_hist 1696 (48, 1, [3; 5],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1697 *)
let HOQ_QUERY1697 = slq_hist 1697 (48, 1, [4; 5],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1698 *)
let HOQ_QUERY1698 = slq_hist 1698 (48, 1, [0; 6],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1699 *)
let HOQ_QUERY1699 = slq_hist 1699 (48, 1, [1; 6],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1700 *)
let HOQ_QUERY1700 = slq_hist 1700 (48, 1, [2; 6],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1701 *)
let HOQ_QUERY1701 = slq_hist 1701 (48, 1, [3; 6],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1702 *)
let HOQ_QUERY1702 = slq_hist 1702 (48, 1, [4; 6],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1703 *)
let HOQ_QUERY1703 = slq_hist 1703 (48, 1, [5; 6],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1704 *)
let HOQ_QUERY1704 = slq_hist 1704 (48, 1, [0; 7],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1705 *)
let HOQ_QUERY1705 = slq_hist 1705 (48, 1, [1; 7],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1706 *)
let HOQ_QUERY1706 = slq_hist 1706 (48, 1, [2; 7],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1707 *)
let HOQ_QUERY1707 = slq_hist 1707 (48, 1, [3; 7],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1708 *)
let HOQ_QUERY1708 = slq_hist 1708 (48, 1, [4; 7],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1709 *)
let HOQ_QUERY1709 = slq_hist 1709 (48, 1, [5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1710 *)
let HOQ_QUERY1710 = slq_hist 1710 (48, 1, [6; 7],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1711 *)
let HOQ_QUERY1711 = slq_hist 1711 (48, 1, [0; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1712 *)
let HOQ_QUERY1712 = slq_hist 1712 (48, 1, [1; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1713 *)
let HOQ_QUERY1713 = slq_hist 1713 (48, 1, [2; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1714 *)
let HOQ_QUERY1714 = slq_hist 1714 (48, 1, [3; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1715 *)
let HOQ_QUERY1715 = slq_hist 1715 (48, 1, [4; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1716 *)
let HOQ_QUERY1716 = slq_hist 1716 (48, 1, [5; 8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query1717 *)
let HOQ_QUERY1717 = slq_hist 1717 (48, 1, [6; 8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query1718 *)
let HOQ_QUERY1718 = slq_hist 1718 (48, 1, [7; 8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query1719 *)
let HOQ_QUERY1719 = slq_hist 1719 (48, 1, [0; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1720 *)
let HOQ_QUERY1720 = slq_hist 1720 (48, 1, [1; 9],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1721 *)
let HOQ_QUERY1721 = slq_hist 1721 (48, 1, [2; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1722 *)
let HOQ_QUERY1722 = slq_hist 1722 (48, 1, [3; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1723 *)
let HOQ_QUERY1723 = slq_hist 1723 (48, 1, [4; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1724 *)
let HOQ_QUERY1724 = slq_hist 1724 (48, 1, [5; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1725 *)
let HOQ_QUERY1725 = slq_hist 1725 (48, 1, [6; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1726 *)
let HOQ_QUERY1726 = slq_hist 1726 (48, 1, [8; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1727 *)
let HOQ_QUERY1727 = slq_hist 1727 (48, 2, [17; 19],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
