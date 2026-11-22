(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries062.lean                          *)
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

(* Lean: query1984 *)
let HOQ_QUERY1984 = slq_hist 1984 (512, 1, [6; 7; 8],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1985 *)
let HOQ_QUERY1985 = slq_hist 1985 (512, 1, [0; 1; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1986 *)
let HOQ_QUERY1986 = slq_hist 1986 (512, 1, [0; 2; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1987 *)
let HOQ_QUERY1987 = slq_hist 1987 (512, 1, [1; 2; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1988 *)
let HOQ_QUERY1988 = slq_hist 1988 (512, 1, [0; 3; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1989 *)
let HOQ_QUERY1989 = slq_hist 1989 (512, 1, [1; 3; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1990 *)
let HOQ_QUERY1990 = slq_hist 1990 (512, 1, [2; 3; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1991 *)
let HOQ_QUERY1991 = slq_hist 1991 (512, 1, [0; 4; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1992 *)
let HOQ_QUERY1992 = slq_hist 1992 (512, 1, [1; 4; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1993 *)
let HOQ_QUERY1993 = slq_hist 1993 (512, 1, [2; 4; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1994 *)
let HOQ_QUERY1994 = slq_hist 1994 (512, 1, [3; 4; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1995 *)
let HOQ_QUERY1995 = slq_hist 1995 (512, 1, [0; 5; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1996 *)
let HOQ_QUERY1996 = slq_hist 1996 (512, 1, [1; 5; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1997 *)
let HOQ_QUERY1997 = slq_hist 1997 (512, 1, [2; 5; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1998 *)
let HOQ_QUERY1998 = slq_hist 1998 (512, 1, [3; 5; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1999 *)
let HOQ_QUERY1999 = slq_hist 1999 (512, 1, [4; 5; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2000 *)
let HOQ_QUERY2000 = slq_hist 2000 (512, 1, [0; 6; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2001 *)
let HOQ_QUERY2001 = slq_hist 2001 (512, 1, [1; 6; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query2002 *)
let HOQ_QUERY2002 = slq_hist 2002 (512, 1, [2; 6; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query2003 *)
let HOQ_QUERY2003 = slq_hist 2003 (512, 1, [3; 6; 9],
  [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query2004 *)
let HOQ_QUERY2004 = slq_hist 2004 (512, 1, [4; 6; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query2005 *)
let HOQ_QUERY2005 = slq_hist 2005 (512, 1, [5; 6; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query2006 *)
let HOQ_QUERY2006 = slq_hist 2006 (512, 1, [0; 7; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2007 *)
let HOQ_QUERY2007 = slq_hist 2007 (512, 1, [1; 7; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query2008 *)
let HOQ_QUERY2008 = slq_hist 2008 (512, 1, [2; 7; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2009 *)
let HOQ_QUERY2009 = slq_hist 2009 (512, 1, [3; 7; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2010 *)
let HOQ_QUERY2010 = slq_hist 2010 (512, 1, [4; 7; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2011 *)
let HOQ_QUERY2011 = slq_hist 2011 (512, 1, [5; 7; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query2012 *)
let HOQ_QUERY2012 = slq_hist 2012 (512, 1, [6; 7; 9],
  [(nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query2013 *)
let HOQ_QUERY2013 = slq_hist 2013 (512, 1, [0; 8; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query2014 *)
let HOQ_QUERY2014 = slq_hist 2014 (512, 1, [1; 8; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query2015 *)
let HOQ_QUERY2015 = slq_hist 2015 (512, 1, [2; 8; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "33/20", nlin_rat "33/20"); (nlin_rat "113/50", nlin_rat "2")]);;
